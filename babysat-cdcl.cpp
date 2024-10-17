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
"  -c <limit>         set conflict limit\n"
"\n"
"and '<dimacs>' is the input file in DIMACS format.  The solver\n"
"reads from '<stdin>' if no input file is specified.\n";

// clang-format on

#include <algorithm>
#include <cassert>
#include <climits>
#include <csignal>
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

// Clause data structure.

struct Clause {
#ifndef NDEBUG
  size_t id;  // For debugging.
#endif
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

static int variables;	     // Variable range: 1 .. <variables>.
static signed char *values;  // Assignment 0=unassigned, -1=false, 1=true.
static unsigned *levels;     // Maps variables to their level.
static Clause **reasons;     // Reasons of forced assignments.

static std::vector<int> analyzed;  // Variables analyzed and thus stamped.
static std::vector<int> learned_clause; // The Clause to be learned
static size_t *stamped;		   // Maps variables to used time stamps.

static std::vector<Clause *> clauses;
static std::vector<Clause *> *matrix;

static Clause *empty_clause;  // Empty clause found.

// Using a fixed size trail makes propagation and backtracking faster.

static int *trail;	 // The start of the assigned literals.
static int *assigned;	 // The end of the assigned literals.
static int *propagated;	 // The end of the propagated literals.

static std::vector<int *> control;

static unsigned level;	// Decision level.

// Conflict limit.

static size_t limit = -1;  // Extends to 'MAX_SIZE_T' ('size_t' unsigned).

// Statistics:

static size_t added;	     // Number of added clauses.
static size_t conflicts;     // Number of conflicts.
static size_t backjumps;     // Number of backjumped levels.
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
	"c              decisions              variables\n"
	"c   seconds                 conflicts           remaining\n"
	"c\n");
  int remaining = variables - fixed;
  printf("c %c %7.2f %12zu %12zu %9d %3.0f%%\n", type, process_time(),
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
    snprintf(res + len, remaining, "@%u=%d", levels[abs(lit)], value);
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
  printf(" size %u clause[%zu]", c->size, c->id);
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

  values = new signed char[twice]();
  matrix = new std::vector<Clause *>[twice];

  levels = new unsigned[size];
  stamped = new size_t[size]();
  reasons = new Clause *[size];

  // We subtract 'variables' in order to be able to access
  // the arrays with a negative index (valid in C/C++).

  matrix += variables;
  values += variables;

  propagated = assigned = trail = new int[size];

  assert(!level);
}

static void delete_clause(Clause *c) {
  debug(c, "delete");
  delete[] c;
}

static void release(void) {
  for (auto c : clauses) delete_clause(c);

  delete[] trail;

  matrix -= variables;
  values -= variables;

  delete[] matrix;
  delete[] values;

  delete[] levels;
  delete[] stamped;
}

static bool satisfied(Clause *c) {
  for (auto lit : *c)
    if (values[lit] > 0) return true;
  return false;
}

static bool satisfied() {
  assert(propagated == assigned);
  return assigned - trail == variables;
}

static void assign(int lit, Clause *reason) {
  debug("assign %s", debug(lit));
  assert(lit);
  assert(!values[lit]);
  assert(!values[-lit]);
  values[lit] = 1;
  values[-lit] = -1;
  int idx = abs(lit);
  levels[idx] = level;
  reasons[idx] = reason;
  *assigned++ = lit;
  if (!level) fixed++;
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
#ifndef NDEBUG
  c->id = added;
#endif
  added++;

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
      assign(unit, 0);
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
// conflicts propagating a literal also detects unit clauses and
// then assign the forced literal by that unit clause.

static Clause *propagate(void) {
  while (propagated != assigned) {
    propagations++;
    int lit = *propagated++;
    debug("propagating %d", lit);
    const auto &occurrences = matrix[-lit];
    for (auto c : occurrences) {
      int unit = 0;
      for (auto other : *c) {
	signed char value = values[other];
	if (value < 0) continue;
	if (value > 0 || unit) goto NEXT_CLAUSE;
	unit = other;
      }
      if (!unit) {
	conflicts++;
	debug(c, "conflicting");
	return c;
      }
      debug(c, "forced %s by", debug(unit));
      assign(unit, c);
    NEXT_CLAUSE:;
    }
  }
  return 0;
}

static bool is_power_of_two(size_t n) { return n && !(n & (n - 1)); }

static int searched = 1;

static void decide(void) {
  decisions++;
  while (assert(searched <= variables), values[searched]) searched++;
  level++;
  debug("decide %d", searched);
  control.push_back(assigned);
  stamped[searched] = 0;
  assign(searched, 0);
  if (is_power_of_two(decisions)) report('d');
}

static void unassign(int lit) {
  debug("unassign %s", debug(lit));
  assert(lit);
  assert(values[lit] == 1);
  assert(values[-lit] == -1);
  values[lit] = values[-lit] = 0;
  int tmp = abs(lit);
  if (tmp < searched) searched = tmp;
}

static void backtrack(unsigned new_level) {
  assert(new_level < level);
  int *before = control[new_level];
  while (assigned != before) unassign(*--assigned);
  control.resize(new_level);
  propagated = before;
  level = new_level;
}

// Heads up: This "solution" is not working at all ...
// I suffer from insomnia at the moment so please excuse my garbage code
// Still handing it in ofcourse as i tried my best, but i got confused a lot
// between the lecture and the information in the forum. 

static void analyze_literal(int lit) {
  int idx = abs(lit);
  assert(values[lit]);
  if (!levels[idx]) return;
  if (stamped[idx] == conflicts) return;
  debug("analyzing literal %s", debug(lit));
  assert(values[lit] < 0);
  // stamp literals in the reason clause using the conflict as first reason.
  stamped[idx] = conflicts;
  if(levels[idx] < level) learned_clause.push_back(lit);
  if (reasons[idx]) analyzed.push_back(idx);
}
// 'analyze' funtion which gets the conflict as argument.
static void analyze(Clause *c) {
  debug(c, "analyzing conflict %zu", conflicts);
  learned_clause.clear();
  for (auto lit : *c) analyze_literal(lit);

  int uip = 0;
  // Then continue finding on the trail a literal which was recently stamped.
  // ↑ i think i interpreted this wrong, i also get prime4 unsat so there seems to be an error with my 3. 
  // I have a lot of trouble with understanding what the statement actually means, forum didn't help
  while (!analyzed.empty()) {
    unsigned idx = analyzed.back();
    analyzed.pop_back();
    Clause *reason = reasons[idx];
    // Alternatively you can just go until the decision of the current level (and use that as UIP).
    if (!reason && levels[idx] == level){
      uip = *control[level];
      //debug("decision as uip %s", uip);
      break;
    }
    if (!reason) continue;
    debug(c, "analyzing %s reason", debug(values[idx] > 0 ? idx : -idx));
    for (auto lit : *reason) analyze_literal(lit);
    
    // if the number of analyzed literals on the current level 
    // becomes one it is the UIP and stop traversal.
    int count = 0;
    int last_lit = 0;
    for (auto lit : analyzed){
      if(levels[abs(lit)] == level){
        count++;
        last_lit = lit;
      }
    }
    if(count == 1){
      assert(last_lit != 0);
      uip = last_lit;
      //debug("found uip %s", uip);
      break;
    }
  }
  // This makes the first few tests work but i think it normaly shouldnt be needed (or better said it's probably needed for cdcl that this if is not there)
  // Seems to be some error in my loop
  if(uip == 0){
    uip = *control.back();
  }
  // All stamped ilterals on lower levels as well as the UIP give
  // you the learned clause.
  assert(stamped[abs(uip)]);
  learned_clause.push_back(uip);
  //add_clause(learned_clause);
  unsigned backtrack_level = level - 1;
  unsigned backjump_level= 0;
  int flip = uip;
  // Find the backjump level as the 
  // largest other level (different from current level) in that clause
  for(auto lit : learned_clause){
    if(levels[abs(lit)] < level && levels[abs(lit)] > backjump_level) backjump_level = levels[abs(lit)];
  }
  // in case that l_c is only the uip backjump_level would be 0, think we would need to prevent that
  if(!backjump_level) backjump_level = backtrack_level;

  unsigned jumped_levels = backtrack_level - backjump_level;
  if (jumped_levels) {
    debug("backjumping over %u levels to level %d to flip %s", jumped_levels,
	  backjump_level, debug(flip));
    backjumps++;
  } else
    debug("backtracking to level %d to flip %s", backtrack_level, debug(flip));
  // Backtrack to that level and assign the UIP to its opposite value (flip it).
  backtrack(backjump_level);
  assign(-flip, 0);
}

// The SAT competition standardized exit codes (the 'exit (code)' or 'return
// res' in 'main').  All other exit codes denote unsolved or error.

static const int unknown = 0;	      // Unsolved exit code.
static const int satisfiable = 10;    // Exit code for satisfiable and
static const int unsatisfiable = 20;  // unsatisfiable formulas.

static int solve(void) {
  if (empty_clause) return unsatisfiable;
  for (;;) {
    Clause *conflict = propagate();
    if (conflict) {
      if (!level) return unsatisfiable;
      analyze(conflict);
    } else if (satisfied())
      return satisfiable;
    else if (conflicts >= limit)
      return unknown;
    else
      decide();
  }
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
static double percent(double a, double b) { return average(100 * a, b); }

// The main function expects at most one argument which is then considered
// as the path to a DIMACS file. Without argument the solver reads from
// '<stdin>' (the standard input connected for instance to the terminal).

static void print_statistics() {
  if (verbosity < 0) return;
  printf("c\n");
  double t = process_time();
  printf("c %-15s %16zu %12.2f per second\n", "conflicts:", conflicts,
	 average(conflicts, t));
  printf("c %-15s %16zu %12.2f per second\n", "decisions:", decisions,
	 average(decisions, t));
  printf("c %-15s %16zu %12.2f %% conflicts\n", "backjumps:", backjumps,
	 percent(backjumps, conflicts));
  printf("c %-15s %16zu %12.2f million per second\n",
	 "propagations:", propagations, average(propagations * 1e-6, t));
  printf("c\n");
  printf("c %-15s %16.2f seconds\n", "process-time:", t);
  printf("c\n");
}

// We have global signal handlers for printing statistics even if
// interrupted or some other error occurs.

static volatile int caught_signal;

struct {
  int sig;
  void (*saved)(int);
} handler[] = {{SIGABRT, 0}, {SIGINT, 0}, {SIGSEGV, 0}, {SIGTERM, 0}};

static const size_t size_handlers = sizeof handler / sizeof *handler;

static void reset_signal_handlers() {
  for (size_t i = 0; i != size_handlers; i++)
    signal(handler[i].sig, handler[i].saved);
}

static void catch_signal(int sig) {
  if (caught_signal) return;
  reset_signal_handlers();
  caught_signal = sig;
  line();
  message("caught signal %d", sig);
  print_statistics();
  message("raising signal %d", sig);
  raise(sig);
}

static void set_signal_handlers() {
  for (size_t i = 0; i != size_handlers; i++)
    handler[i].saved = signal(handler[i].sig, catch_signal);
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
    else if (!strcmp(arg, "-c")) {
      if (++i == argc) die("argument to '-c' missing");
      limit = atol(argv[i]);
    } else if (arg[0] == '-')
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

  message("BabySAT CDCL SAT Solver");
  line();
  message("Copyright (c) 2022-2023, Marek Schuster");
  message("Version %s %s", VERSION, GITID);
  message("Compiled with '%s'", BUILD);
  line();
  message("reading from '%s'", file_name);

  set_signal_handlers();

  parse();

  verbose("solving with conflict limit %zu", limit);

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
  reset_signal_handlers();

  print_statistics();
  message("exit code %d", res);

  return res;
}
