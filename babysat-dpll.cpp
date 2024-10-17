// clang-format off

const char *usage =
"usage: babysat [ <option> ... ] [ <dimacs> ]\n"
"\n"
"where '<option>' can be one of the following\n"
"\n"
"  -h | --help        print this command line option summary\n"
#ifdef LOGGING
"  -l | --logging     print very verbose logging information\n"
#endif
"  -q | --quiet       do not print any messages\n"
"  -n | --no-witness  do not print witness if satisfiable\n"
"  -v | --verbose     print verbose messages\n"
"\n"
"and '<dimacs>' is the input file in DIMACS format.  The solver\n"
"reads from '<stdin>' if no input file is specified.\n";

// clang-format on

#include <algorithm>
#include <cassert>
#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

// Linux/Unix system specific.

#include <sys/resource.h>
#include <sys/time.h>

// Global options accessible through the command line.

static bool witness = true;

static int verbosity;  // -1=quiet, 0=normal, 1=verbose, INT_MAX=logging

// Global options fixed at compile time.

struct Clause {
  unsigned id;	// For debugging and sorting.
  unsigned size;
  int literals[];

  // The following two functions allow simple ranged-based for-loop
  // iteration over Clause literals with the following idiom:
  //
  //   Clause *c = ...
  //   for (auto lit : *c)
  //     do_something_with (lit);
  //
  int *begin() { return literals; }
  int *end() { return literals + size; }
};

static int variables;	     // Variable range: 1,..,<variables>
static signed char *values;  // Assignment 0=unassigned,-1=false,1=true.
static unsigned *levels;     // Maps variables to their level;

static std::vector<Clause *> clauses;
static std::vector<Clause *> *matrix;

static Clause *empty_clause;  // Empty clause found.

static std::vector<int> trail;
static std::vector<size_t> control;

static unsigned level;	   // Decision level.
static size_t propagated;  // Next position on trail to propagate.

static bool init;

// Statistics:

static size_t added;	     // Number of added clauses.
static size_t conflicts;     // Number of conflicts.
static size_t decisions;     // Number of decisions.
static size_t propagations;  // Number of propagated literals.
static size_t reports;	     // Number of calls to 'report'.
static int fixed;	     // Number of root-level assigned variables.

// Get process-time of this process.  This is not portable to Windows but
// should work on other Unixes such as MacOS as is.

static double process_time(void) {
  struct rusage u;
  double res;
  if (getrusage(RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

// Report progress once in a while.

static void report(char type) {
  if (verbosity < 0) return;
  if (!(reports++ % 20))
    printf(
	"c\n"
	"c             decisions             variables\n"
	"c   seconds              conflicts            remaining\n"
	"c\n");
  int remaining = variables - fixed;
  printf("c %c %7.2f %11zu %11zu %9d %3.0f%%\n", type, process_time(),
	 decisions, conflicts, remaining,
	 variables ? 100.0 * remaining / variables : 0);
  fflush(stdout);
}

// Generates nice compiler warnings if format string does not fit arguments.

static void message(const char *, ...) __attribute__((format(printf, 1, 2)));
static void die(const char *, ...) __attribute__((format(printf, 1, 2)));

static void parse_error(const char *fmt, ...)
    __attribute__((format(printf, 1, 2)));

#ifdef LOGGING

static void debug(const char *, ...) __attribute__((format(printf, 1, 2)));

static void debug(Clause *, const char *, ...)
    __attribute__((format(printf, 2, 3)));

static bool logging() { return verbosity == INT_MAX; }

// Print debugging message if '--debug' is used.  This is only enabled
// if the solver is configured with './configure --logging' (which is the
// default for './configure --debug').  Even if logging code is included
// this way, it still needs to be enabled at run-time through '-l'.

static char debug_buffer[4][32];
static size_t next_debug_buffer;

// Get a statically allocate string buffer.
// Used here only for printing literals.

static char *debug_string(void) {
  char *res = debug_buffer[next_debug_buffer++];
  if (next_debug_buffer == sizeof debug_buffer / sizeof *debug_buffer)
    next_debug_buffer = 0;
  return res;
}

static char *debug(int lit) {
  if (!logging()) return 0;
  char *res = debug_string();
  sprintf(res, "%d", lit);
  int value = values[lit];
  if (value) {
    size_t len = strlen(res);
    size_t remaining = sizeof debug_buffer[0] - len;
    snprintf(res + len, remaining, "@%u=%d", levels[abs(lit)], level);
  }
  assert(strlen(res) <= sizeof debug_buffer[0]);
  return res;
}

static void debug_prefix(void) { printf("c DEBUG %u ", level); }

static void debug_suffix(void) {
  fputc('\n', stdout);
  fflush(stdout);
}

static void debug(const char *fmt, ...) {
  if (!logging()) return;
  debug_prefix();
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  debug_suffix();
}

static void debug(Clause *c, const char *fmt, ...) {
  if (!logging()) return;
  debug_prefix();
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  printf(" size %u clause[%u]", c->size, c->id);
  for (auto lit : *c) printf(" %s", debug(lit));
  debug_suffix();
}

#else

#define debug(...) \
  do {             \
  } while (0)

#endif

// Print message to '<stdout>' and flush it.

static void message(const char *fmt, ...) {
  if (verbosity < 0) return;
  fputs("c ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

static void line() {
  if (verbosity < 0) return;
  fputs("c\n", stdout);
  fflush(stdout);
}

static void verbose(const char *fmt, ...) {
  if (verbosity <= 0) return;
  fputs("c ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

// Print error message and 'die'.

static void die(const char *fmt, ...) {
  fprintf(stderr, "babysat: error: ");
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void initialize(void) {
  assert(variables < INT_MAX);
  unsigned size = variables + 1;

  unsigned twice = 2 * size;

  values = new signed char[twice];
  matrix = new std::vector<Clause *>[twice];

  levels = new unsigned[size];

  // We subtract 'variables' in order to be able to access
  // the arrays with a negative index (valid in C/C++).

  matrix += variables;
  values += variables;

  for (int lit = -variables; lit <= variables; lit++) values[lit] = 0;

  assert(!propagated);
  assert(!level);
}

static void delete_clause(Clause *c) {
  debug(c, "delete");
  delete[] c;
}

static void release(void) {
  for (auto c : clauses) delete_clause(c);

  matrix -= variables;
  values -= variables;

  delete[] matrix;
  delete[] values;

  delete[] levels;
}

static bool satisfied(Clause *c) {
  for (auto lit : *c)
    if (values[lit] > 0) return true;
  return false;
}

// Check whether all clauses are satisfied.

static bool satisfied() { 
  //from lecture: for (auto c: Clause)
  for(auto c : clauses)
    if (!satisfied(c)) return false;
  return true; }

static void assign(int lit) {
  debug("assign %s", debug(lit));
  assert(lit);
  assert(!values[lit]);
  assert(!values[-lit]);
  // Set 'values[lit]' and 'values[-lit]'.
  values[lit] = 1;
  values[-lit] = -1;
  // Set 'levels[abs(lit)]'.
  levels[abs(lit)] = level;
  // Push literal on trail.
  trail.push_back(lit);
  // If root-level (so level == 0) increase fixed.
  if(level == 0) 
    fixed++;
}

static void connect_literal(int lit, Clause *c) {
  debug(c, "connecting %s to", debug(lit));
  matrix[lit].push_back(c);
}

static Clause *add_clause(std::vector<int> &literals) {
  size_t size = literals.size();
  size_t bytes = sizeof(struct Clause) + size * sizeof(int);
  Clause *c = (Clause *)new char[bytes];

  assert(size <= UINT_MAX);
  c->id = added++;

  assert(clauses.size() <= (size_t)INT_MAX);
  c->size = size;

  int *q = c->literals;
  for (auto lit : literals) *q++ = lit;

  debug(c, "new");

  clauses.push_back(c);	 // Save it on global stack of clauses.

  // Connect the literals of the clause in the matrix.

  for (auto lit : *c) connect_literal(lit, c);

  // Handle the special case of empty and unit clauses.

  if (!size) {
    debug(c, "parsed empty clause");
    empty_clause = c;
  } else if (size == 1) {
    int unit = literals[0];
    signed char value = values[unit];
    if (!value)
      assign(unit);
    else if (value < 0) {
      debug(c, "inconsistent unit clause");
      empty_clause = c;
    }
  }

  return c;
}

static const char *file_name;
static bool close_file;
static FILE *file;

static void parse_error(const char *fmt, ...) {
  fprintf(stderr, "babysat: parse error in '%s': ", file_name);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void parse(void) {
  int ch;
  while ((ch = getc(file)) == 'c') {
    while ((ch = getc(file)) != '\n')
      if (ch == EOF) parse_error("end-of-file in comment");
  }
  if (ch != 'p') parse_error("expected 'c' or 'p'");
  int clauses;
  if (fscanf(file, " cnf %d %d", &variables, &clauses) != 2 || variables < 0 ||
      variables >= INT_MAX || clauses < 0 || clauses >= INT_MAX)
    parse_error("invalid header");
  message("parsed header 'p cnf %d %d'", variables, clauses);
  initialize();
  std::vector<int> clause;
  int lit = 0, parsed = 0;
  size_t literals = 0;
  while (fscanf(file, "%d", &lit) == 1) {
    if (parsed == clauses) parse_error("too many clauses");
    if (lit == INT_MIN || abs(lit) > variables)
      parse_error("invalid literal '%d'", lit);
    if (lit) {
      clause.push_back(lit);
      literals++;
    } else {
      add_clause(clause);
      clause.clear();
      parsed++;
    }
  }
  if (lit) parse_error("terminating zero missing");
  if (parsed != clauses) parse_error("clause missing");
  if (close_file) fclose(file);
  verbose("parsed %zu literals in %d clauses", literals, parsed);
}

// Return 'false' if propagation detects an empty clause otherwise if it
// completes propagating all literals since the last time it was called
// without finding an empty clause it returns 'true'.  Beside finding
// conflict propagating a literal also detects unit clauses and
// then assign the forced literal by that unit clause.

static bool propagate(void) {
  // While not all literals propagated.
  //int i = 0;
  while (propagated < trail.size())
  {
    propagations++;
    auto lit = trail[propagated++];
    
    for(auto c: matrix[-lit]){

      //check satisfied
      if(satisfied(c))
        continue;
      //check falsified / forcing
      
      int unassigned = 0;
      int unassigned_lit;
      for(auto literal: *c){
        if(values[literal] == 0){
          unassigned++;
          unassigned_lit = literal;
        }
      }
      switch (unassigned)
      {
      case 0:       //falsified
        conflicts++;
        return false;
      case 1:       //forcing
        assign(unassigned_lit);
        break;
      default:
        continue;
      }
      break;
    }
    }
    
  
  // Propagated next literal 'lit' on trail.
  // Increase 'propagations'.
  // Go over all clauses in which '-lit' occurs.
  // For each clause check whether it is satisfied, falsified, or forcing.
  // If clause falsified return 'false' (increase 'conflicts').
  // If forcing assign the forced unit.
  // If all literals propagated without finding a falsified clause (conflict):
  return true;
}

static int is_power_of_two(size_t n) { return n && !(n & (n - 1)); }

static int decide(void) {
  decisions++;
  int res = 0;
  // Find a variable/literal which is not assigned yet.
  for (int i=1; i<= variables; i++){
    if(values[i] == 0){
      res = i;
      break;
    } 
  }
  // Increase decision level.
  level++;
  // Save the current trail on the control stack for backtracking.
  control.push_back(trail.size());
  // Assign the picked decision literal.
  assign(res);
  if (is_power_of_two(decisions)) report('d');
  return res;
}

static void unassign(int lit) {
  debug("unassign %s", debug(lit));
  // Reset 'values[lit]' and 'values[-lit]'.
  values[lit] = 0;
  values[-lit] = 0;
}

static void backtrack() {
  assert(level);
  debug("backtracking to level %d", level - 1);
  // Pop previous trail from control stack.
  auto old_height = control.back();
  control.pop_back();
  // Unassign all literals starting from previous to current trail height.
  while (trail.size() > old_height)
  {
    unassign(trail.back());
    trail.pop_back();
  }
  // Set 'propagted' to trail height.
  propagated = trail.size();
  // Decrement decision level.
  level--;
}

// The SAT competition standardized exit codes (the 'exit (code)' or 'return
// res' in 'main').  All other exit codes denote unsolved or error.

static const int satisfiable = 10;    // Exit code for satisfiable and
static const int unsatisfiable = 20;  // unsatisfiable formulas.

static int dpll(void) { 
  for (;;){
    if(!propagate()) return unsatisfiable;
    if(satisfied()) return satisfiable;
    int x = decide();
    if(dpll() == satisfiable) return satisfiable;
    backtrack();
    assign(-x);
  }
 }

static int solve(void) {
  if (empty_clause) return unsatisfiable;
  return dpll();
}

// Checking the model on the original formula is extremely useful for
// testing and debugging.  This 'checker' aborts if an unsatisfied clause is
// found and prints the clause on '<stderr>' for debugging purposes.

static void check_model(void) {
  debug("checking model");
  for (auto c : clauses) {
    if (satisfied(c)) continue;
    fputs("babysat: unsatisfied clause:\n", stderr);
    for (auto lit : *c) fprintf(stderr, "%d ", lit);
    fputs("0\n", stderr);
    fflush(stderr);
    abort();
    exit(1);
  }
}

// Printing the model in the format of the SAT competition, e.g.,
//
//   v -1 2 3 0
//
// Always prints a full assignments even if not all values are set.

static void print_model(void) {
  printf("v ");
  for (int idx = 1; idx <= variables; idx++) {
    if (values[idx] < 0) printf("-");
    printf("%d ", idx);
  }
  printf("0\n");
}

static double average(double a, double b) { return b ? a / b : 0; }

// The main function expects at most one argument which is then considered
// as the path to a DIMACS file. Without argument the solver reads from
// '<stdin>' (the standard input connected for instance to the terminal).

static void print_statistics() {
  double t = process_time();
  printf("c %-15s %16zu %12.2f per second\n", "conflicts:", conflicts,
	 average(conflicts, t));
  printf("c %-15s %16zu %12.2f per second\n", "decisions:", decisions,
	 average(decisions, t));
  printf("c %-15s %16zu %12.2f million per second\n",
	 "propagations:", propagations, average(propagations * 1e-6, t));
  printf("c\n");
  printf("c %-15s %16.2f seconds\n", "process-time:", t);
}

#include "config.hpp"

int main(int argc, char **argv) {
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h") || !strcmp(arg, "--help")) {
      fputs(usage, stdout);
      exit(0);
    } else if (!strcmp(arg, "-l") || !strcmp(arg, "--logging"))
#ifdef LOGGING
      verbosity = INT_MAX;
#else
      die("compiled without logging code (use './configure --logging')");
#endif
    else if (!strcmp(arg, "-q") || !strcmp(arg, "--quiet"))
      verbosity = -1;
    else if (!strcmp(arg, "-v") || !strcmp(arg, "--verbose"))
      verbosity = 1;
    else if (!strcmp(arg, "-n") || !strcmp(arg, "--no-witness"))
      witness = false;
    else if (arg[0] == '-')
      die("invalid option '%s' (try '-h')", arg);
    else if (file_name)
      die("too many arguments '%s' and '%s' (try '-h')", file_name, arg);
    else
      file_name = arg;
  }

  if (!file_name) {
    file_name = "<stdin>";
    assert(!close_file);
    file = stdin;
  } else if (!(file = fopen(file_name, "r")))
    die("could not open and read '%s'", file_name);
  else
    close_file = true;

  message("BabySAT DPLL SAT Solver");
  line();
  message("Copyright (c) 2022-2023, Marek Schuster");
  message("Version %s %s", VERSION, GITID);
  message("Compiled with '%s'", BUILD);
  line();
  message("reading from '%s'", file_name);

  parse();
  report('*');

  int res = solve();
  report(res == 10 ? '1' : res == 20 ? '0' : '?');
  line();

  if (res == 10) {
    check_model();
    printf("s SATISFIABLE\n");
    if (witness) print_model();
  } else if (res == 20)
    printf("s UNSATISFIABLE\n");

  release();

  if (verbosity >= 0) line(), print_statistics(), line();

  message("exit code %d", res);

  return res;
}

//Lecture notes
//bfs is important (i think for trail)