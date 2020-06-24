/*-------------------------------------------------------------------------*/
/* Copyright 2010-2020 Armin Biere Johannes Kepler University Linz Austria */
/*-------------------------------------------------------------------------*/

#include "lglib.h"
#include "aiger.h"
#include "ccadical.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct Clause
{
  int *lits;
} Clause;

static aiger *model;
static unsigned num_bad;
static aiger_symbol *badsyms;
static FILE *outfile, *msgfile, *errfile, *apitrace;
static int verbose, xstim, plain, nowitness, noclone;
static LGL *lgl, *clone;
static int *coi, opt = 3;
static int cloned;

/* It seems cadical C API does not allow to extract clauses. Hence we
   use the flag 'cadical_extracting_clauses' to indicate whether we map
   literals in clauses that are added to cadical. Mapping of literals is
   only necessary once before main BMC loop (see 'extract' function). */
static int use_cadical = 0, cadical_extracting_clauses = 0;
static CCaDiCaL *cadical = 0;
static void extract (void *, int);


static Clause *clauses;
static int nclauses, szclauses;

static int *lits;
static int nlits, szlits;

static int maxvar;
static int *litmap;
static int k;

static size_t maxbytes, curbytes;

static int catchedsig;
static void (*sig_int_handler) (int);
static void (*sig_segv_handler) (int);
static void (*sig_abrt_handler) (int);
static void (*sig_term_handler) (int);

static void
resetsighandlers (void)
{
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
}

static void
msg (int level, const char *fmt, ...)
{
  va_list ap;
  if (verbose < level)
    return;
  fprintf (msgfile, "c [blimc] %.2f ", !use_cadical ? lglprocesstime () : 0);
  va_start (ap, fmt);
  vfprintf (msgfile, fmt, ap);
  va_end (ap);
  fputc ('\n', msgfile);
  fflush (msgfile);
}

static void
caughtsigmsg (int sig)
{
  if (!verbose)
    return;
  fprintf (errfile, "c [blimc]\nc [blimc] CAUGHT SIGNAL %d\nc [blimc]\n",
	   sig);
  fflush (errfile);
}

static void
stats (void)
{
  if (verbose)
    {
      if (use_cadical)
        ccadical_print_statistics (cadical);
      else
        {
          if (clone)
            lglstats (clone);
          if (lgl)
            lglstats (lgl);
        }
    }
  msg (1, "reached k = %d", k);
  msg (1, "cloned %d solvers", cloned);
  msg (1, "max %.1f MB", maxbytes / (double) (1 << 20));
}

static void
catchsig (int sig)
{
  if (!catchedsig)
    {
      fputs ("s UNKNOWN\n", errfile);
      fflush (errfile);
      catchedsig = 1;
      caughtsigmsg (sig);
      if (verbose)
	stats (), caughtsigmsg (sig);
    }
  resetsighandlers ();
  if (!getenv ("LGLNABORT"))
    raise (sig);
  else
    exit (1);
}

static void
setsighandlers (void)
{
  sig_int_handler = signal (SIGINT, catchsig);
  sig_segv_handler = signal (SIGSEGV, catchsig);
  sig_abrt_handler = signal (SIGABRT, catchsig);
  sig_term_handler = signal (SIGTERM, catchsig);
}

static void
die (const char *fmt, ...)
{
  va_list ap;
  fputs ("*** blimc: ", errfile);
  va_start (ap, fmt);
  vfprintf (errfile, fmt, ap);
  va_end (ap);
  fputc ('\n', errfile);
  fflush (errfile);
  exit (1);
}

static void *
new (void *state, size_t bytes)
{
  char *res;
  (void) state;
  res = malloc (bytes);
  if (!res)
    die ("out of memory");
  curbytes += bytes;
  if (curbytes > maxbytes)
    maxbytes = curbytes;
  return res;
}

static void
del (void *state, void *ptr, size_t bytes)
{
  (void) state;
  assert (curbytes >= bytes);
  curbytes -= bytes;
  free (ptr);
}

static void *
rsz (void *state, void *ptr, size_t o, size_t n)
{
  char *res;
  (void) state;
  assert (curbytes >= o);
  curbytes -= o;
  res = realloc (ptr, n);
  if (!res)
    die ("out of memory");
  curbytes += n;
  if (curbytes > maxbytes)
    maxbytes = curbytes;
  return res;
}

static int
prepilit (unsigned ulit)
{
  int res;
  assert (aiger_lit2var (ulit) <= model->maxvar);
  assert (coi[aiger_lit2var (ulit)]);
  assert (ulit <= 2 * model->maxvar + 1);
  res = (ulit >> 1) + 1;
  if (ulit & 1)
    res = -res;
  return res;
}

static unsigned
aiginput (unsigned idx)
{
  assert (idx < model->num_inputs);
  return model->inputs[idx].lit;
}

static int
prepinput (unsigned idx)
{
  return prepilit (aiginput (idx));
}

static unsigned
aiglatch (unsigned idx)
{
  assert (idx < model->num_latches);
  return model->latches[idx].lit;
}

static unsigned
aigreset (unsigned idx)
{
  assert (idx < model->num_latches);
  return model->latches[idx].reset;
}

static int
preplatch (unsigned idx)
{
  return prepilit (aiglatch (idx));
}

static unsigned
aignext (unsigned idx)
{
  assert (idx < model->num_latches);
  return model->latches[idx].next;
}

static int
prepnext (unsigned idx)
{
  return prepilit (aignext (idx));
}

static unsigned
aigbad (unsigned idx)
{
  assert (idx < num_bad);
  return badsyms[idx].lit;
}

static int
prepbad (unsigned idx)
{
  return prepilit (aigbad (idx));
}

static int
preplhs (unsigned idx)
{
  assert (idx < model->num_ands);
  return prepilit (model->ands[idx].lhs);
}

static int
prepleft (unsigned idx)
{
  assert (idx < model->num_ands);
  return prepilit (model->ands[idx].rhs0);
}

static int
prepright (unsigned idx)
{
  assert (idx < model->num_ands);
  return prepilit (model->ands[idx].rhs1);
}

static void
unit (int ilit)
{
  fprintf (stderr, "DEBUG: add unit clause '%d 0'\n", ilit);
  
  if (!use_cadical)
    {
      lgladd (lgl, ilit);
      lgladd (lgl, 0);
    }
  else
    {
      ccadical_add (cadical, ilit);
      if (cadical_extracting_clauses)
        extract ((void *) 0, ilit);
      
      ccadical_add (cadical, 0);
      if (cadical_extracting_clauses)
        extract ((void *) 0, 0);
    }
}

static void
binary (int a, int b)
{
  fprintf (stderr, "DEBUG: add binary clause '%d %d 0'\n", a, b);
  
  if (!use_cadical)
    {
      lgladd (lgl, a);
      lgladd (lgl, b);
      lgladd (lgl, 0);
    }
  else
    {
      ccadical_add (cadical, a);
      if (cadical_extracting_clauses)
        extract ((void*) 0, a);
      
      ccadical_add (cadical, b);
      if (cadical_extracting_clauses)
        extract ((void*) 0, b);
      
      ccadical_add (cadical, 0);
      if (cadical_extracting_clauses)
        extract ((void*) 0, 0);      
    }
}

static void
ternary (int a, int b, int c)
{
  fprintf (stderr, "DEBUG: add ternary clause '%d %d %d 0'\n", a, b, c);
  
  if (!use_cadical)
    {
      lgladd (lgl, a);
      lgladd (lgl, b);
      lgladd (lgl, c);
      lgladd (lgl, 0);
    }
  else
    {
      ccadical_add (cadical, a);
      if (cadical_extracting_clauses)
        extract ((void*) 0, a);

      ccadical_add (cadical, b);
      if (cadical_extracting_clauses)
        extract ((void*) 0, b);

      ccadical_add (cadical, c);
      if (cadical_extracting_clauses)
        extract ((void*) 0, c);

      ccadical_add (cadical, 0);
      if (cadical_extracting_clauses)
        extract ((void*) 0, 0);
    }
}

static int
ulitincoi (unsigned ulit)
{
  unsigned idx;
  assert (ulit <= 2 * model->maxvar + 1);
  idx = aiger_lit2var (ulit);
  assert (idx <= model->maxvar);
  return coi[idx];
}

static void
prepfreeze (void)
{
  assert (!use_cadical);
  unsigned i;
  msg (2, "freeze");
  for (i = 0; i < model->num_inputs; i++)
    if (!nowitness && ulitincoi (aiginput (i)))
      lglfreeze (lgl, prepinput (i));
  for (i = 0; i < model->num_latches; i++)
    {
      if (!ulitincoi (aiglatch (i)))
	continue;
      lglfreeze (lgl, preplatch (i));
      lglfreeze (lgl, prepnext (i));
    }
  for (i = 0; i < num_bad; i++)
    {
      assert (ulitincoi (badsyms[i].lit));
      lglfreeze (lgl, prepbad (i));
    }
  if (ulitincoi (0))
    lglfreeze (lgl, 1);
}

static void
and (int lhs, int rhs0, int rhs1)
{
  fprintf (stderr, "DEBUG: and \n");
  binary (-lhs, rhs0);
  binary (-lhs, rhs1);
  ternary (-rhs0, -rhs1, lhs);
}

static void
logic (void)
{
  fprintf (stderr, "DEBUG: logic \n");
  unsigned i;
  msg (2, "logic");
  if (ulitincoi (0))
    unit (-1);
  for (i = 0; i < model->num_ands; i++)
    {
      if (ulitincoi (model->ands[i].lhs))
        and (preplhs (i), prepleft (i), prepright (i));
    }
  fprintf (stderr, "DEBUG: done logic \n");
}

static const char *usage =
  "usage: blimc [-h][-v][-x][-n][-p][-O[0123]][--no-clone][--use-cadical][<maxk>][<aiger>]\n";

static int
isnumstr (const char *str)
{
  const char *p = str;
  int ch;
  if (!isdigit (*p++))
    return 0;
  while (isdigit ((ch = *p)))
    p++;
  return !ch;
}

static double
percent (double a, double b)
{
  return b ? 100.0 * (a / b) : 0.0;
}

static void
coimsg (const char *name, unsigned remaining, unsigned all)
{
  msg (1, "%-9s in COI: %10u = %3.0f%% out of %u",
       name, remaining, percent (remaining, all), all);
}

static void
travcoi (void)
{
  unsigned next, top, size, latches, inputs, ands, constants;
  unsigned lit, *stack, idx, stripped;
  aiger_symbol *s;
  aiger_and *a;
  size = model->maxvar + 1;
  stack = new (0, size * sizeof *stack);
  latches = inputs = ands = constants = 0;
  assert (num_bad == 1);
  lit = badsyms[0].lit;
  idx = aiger_lit2var (lit);
  coi[idx] = top = next = 1;
  for (;;)
    {
      assert (idx <= model->maxvar);
      assert (coi[idx]);
      stripped = aiger_strip (lit);
      if (aiger_is_input (model, stripped))
	inputs++;
      else if ((s = aiger_is_latch (model, stripped)))
	{
	  latches++;
	  lit = s->next;
	  idx = aiger_lit2var (lit);
	  assert (idx <= model->maxvar);
	  if (!coi[idx])
	    stack[top++] = lit, coi[idx] = top;
	}
      else if ((a = aiger_is_and (model, stripped)))
	{
	  ands++;
	  lit = a->rhs0;
	  idx = aiger_lit2var (lit);
	  assert (idx <= model->maxvar);
	  if (!coi[idx])
	    stack[top++] = lit, coi[idx] = top;
	  lit = a->rhs1;
	  idx = aiger_lit2var (lit);
	  assert (idx <= model->maxvar);
	  if (!coi[idx])
	    stack[top++] = lit, coi[idx] = top;
	}
      else
	assert (!stripped), constants++;
      if (next == top)
	break;
      lit = stack[next++];
    }
  del (0, stack, size * sizeof *stack);
  coimsg ("literals", top, model->maxvar);
  coimsg ("inputs", inputs, model->num_inputs);
  coimsg ("latches", latches, model->num_latches);
  coimsg ("constants", constants, 1);
  coimsg ("ands", ands, model->num_ands);
}

static void
newlgl (int setapitrace)
{
  assert (!use_cadical);
  const char *apitracename = getenv ("BLIMCLGLAPITRACE");
  lgl = lglminit (0, new, rsz, del);
  if (setapitrace && apitracename)
    {
      assert (!apitrace);
      apitrace = fopen (apitracename, "w");
      if (!apitrace)
	die ("can write to API trace file '%s'", apitracename);
      lglwtrapi (lgl, apitrace);
    }
  lglsetout (lgl, msgfile);
  if (verbose >= 2)
    lglsetopt (lgl, "verbose", verbose - 1);
  if (plain)
    lglsetopt (lgl, "plain", 1);
}

static void
extract (void *dummy, int lit)
{
  assert (!use_cadical || cadical_extracting_clauses);
  size_t oldbytes, newbytes;
  Clause *c;
  int i;
  (void) dummy;
  if (lit)
    {
      if (nlits == szlits)
	{
	  oldbytes = szlits * sizeof *lits;
	  szlits = szlits ? 2 * szlits : 1;
	  newbytes = szlits * sizeof *lits;
	  lits = rsz (0, lits, oldbytes, newbytes);
	}
      lits[nlits++] = lit;
    }
  else
    {
      if (nclauses == szclauses)
	{
	  oldbytes = szclauses * sizeof *clauses;
	  szclauses = szclauses ? 2 * szclauses : 1;
	  newbytes = szclauses * sizeof *clauses;
	  clauses = rsz (0, clauses, oldbytes, newbytes);
	}
      c = clauses + nclauses++;
      newbytes = (nlits + 1) * sizeof *c->lits;
      c->lits = new (0, newbytes);
      for (i = 0; i < nlits; i++)
	c->lits[i] = lits[i];
      c->lits[i] = 0;
      nlits = 0;
    }
}

static int
mapuntimedlit (int lit)
{
  int idx = abs (lit), res;
  assert (1 <= idx && idx <= (int) model->maxvar + 1);
  if (!(res = litmap[idx]))
    litmap[idx] = res = ++maxvar;
  if (lit < 0)
    res = -res;
  return res;
}

static void
mapcnf (void)
{
  int *p, lit;
  Clause *c;
  for (c = clauses; c < clauses + nclauses; c++)
    for (p = c->lits; (lit = *p); p++)
      *p = mapuntimedlit (lit);
}

static int
mainilit (unsigned ulit)
{
  int tmp = prepilit (ulit), idx = abs (tmp), res;
  assert (1 <= idx && idx <= (int) model->maxvar + 1);
  res = litmap[idx];
  if (tmp < 0)
    res = -res;
  return res;
}

static int
shift (int ilit, int time)
{
  int idx = abs (ilit), res;
  assert (1 <= idx && idx <= maxvar);
  res = idx + time * maxvar;
  if (ilit < 0)
    res = -res;
  return res;
}

static void
equiv (int a, int b)
{
  fprintf (stderr, "DEBUG: adding equiv \n");
  binary (-a, b);
  binary (a, -b);
}

static void
shiftcnf (int time)
{
  fprintf (stderr, "DEBUG: shiftcnf \n");
  assert (!cadical_extracting_clauses);
  int *p, lit, prev;
  unsigned i;
  Clause *c;
  assert (0 <= time);
  if (time > 0)
    {
      for (i = 0; i < model->num_latches; i++)
	{
	  if (!ulitincoi (aiglatch (i)))
	    continue;
	  prev = shift (mainilit (aignext (i)), time - 1);
	  lit = shift (mainilit (aiglatch (i)), time);
	  equiv (prev, lit);
          if (!use_cadical)
            lglmelt (lgl, prev);
	}
    }
  for (c = clauses; c < clauses + nclauses; c++)
    {
      fprintf (stderr, "DEBUG shiftcnf: add clause: ");
      for (p = c->lits; (lit = *p); p++)
        {
          //DEBUG
          fprintf (stderr, "%d ", shift (lit, time));
          if (!use_cadical)
            lgladd (lgl, shift (lit, time));
          else
            ccadical_add (cadical, shift (lit, time));
        }
      if (!use_cadical)
        lgladd (lgl, 0);
      else
        ccadical_add (cadical, 0);
      //DEBUG
      fprintf (stderr, "0\n");
    }
  for (i = 0; i < model->num_latches; i++)
    if (ulitincoi (aiglatch (i)))
      if (!use_cadical)
        lglfreeze (lgl, shift (mainilit (aignext (i)), time));

  fprintf (stderr, "DEBUG: shiftcnf done\n");
}

static void
bad (LGL * whichlgl, int time)
{
  fprintf (stderr, "DEBUG: assume bad %d\n", shift (mainilit (aigbad (0)), time));
  if (!use_cadical)
    lglassume (whichlgl, shift (mainilit (aigbad (0)), time));
  else
    ccadical_assume (cadical, shift (mainilit (aigbad (0)), time));
}

static void
init (void)
{
  fprintf (stderr, "DEBUG: init \n");
  size_t bytes;
  unsigned i;
  int lit;
  bytes = (model->maxvar + 2) * sizeof *litmap;
  litmap = new (0, bytes);
  memset (litmap, 0, bytes);
  assert (!maxvar);
  maxvar = 0;			// true lit
  for (i = 0; i < model->num_latches; i++)
    {
      if (!ulitincoi (aiglatch (i)))
	continue;
      lit = ++maxvar;
      litmap[preplatch (i)] = lit;
    }
  for (i = 0; i < model->num_inputs; i++)
    {
      if (!ulitincoi (aiginput (i)))
	continue;
      lit = ++maxvar;
      litmap[prepinput (i)] = lit;
    }
  mapcnf ();
  for (i = 0; i < model->num_latches; i++)
    if (ulitincoi (aiglatch (i)))
      (void) mapuntimedlit (prepnext (i));
  msg (1, "mapped %d variables", maxvar);
#ifndef NDEBUG
  for (i = 0; i < num_bad; i++)
    if (ulitincoi (aigbad (i)))
      assert (litmap[abs (prepbad (i))]);
#endif
  fprintf (stderr, "DEBUG: init latches pass \n");
  for (i = 0; i < model->num_latches; i++)
    {
      if (!ulitincoi (aiglatch (i)))
	continue;
      if (aiglatch (i) == aigreset (i))
	continue;
      if (aiger_false == aigreset (i))
	unit (-mainilit (aiglatch (i)));
      if (aiger_true == aigreset (i))
	unit (mainilit (aiglatch (i)));
    }
  fprintf (stderr, "DEBUG: init done \n");
}

static int
length (const int *p)
{
  const int *q;
  for (q = p; *q; q++)
    ;
  return q - p;
}

int
main (int argc, char **argv)
{

  /* TODO add option: disable COI and check impact w/o using cadical/lingeling. */

  /* TODO: add SAT solver API call wrapper to avoid 'if (!use_cadical)...' all the time. */
  
  int res, i, lit, maxk, val;
  unsigned j, init0, init1, initx;
  const char *iname, *err;
  size_t coibytes;
  char prefix[80];
#ifndef NDEBUG
  int fres;
#endif
  LGL *tmp;
  char vch;

  outfile = stdout, msgfile = errfile = stderr;
  iname = 0;
  maxk = 0;

  for (i = 1; i < argc; i++)
    {
      if (!strcmp (argv[i], "-h"))
	{
	  fputs (usage, outfile);
	  exit (0);
	}
      else if (!strcmp (argv[i], "-v"))
	verbose++;
      else if (!strcmp (argv[i], "-x"))
	xstim = 1;
      else if (!strcmp (argv[i], "-n"))
	nowitness = 1;
      else if (!strcmp (argv[i], "-p"))
	plain = 1;
      else if (!strcmp (argv[i], "-O"))
	opt = 1;
      else if (!strcmp (argv[i], "-O0"))
	opt = 0;
      else if (!strcmp (argv[i], "-O1"))
	opt = 1;
      else if (!strcmp (argv[i], "-O2"))
	opt = 2;
      else if (!strcmp (argv[i], "-O3"))
	opt = 3;
      else if (!strcmp (argv[i], "--no-clone"))
	noclone = 1;
      else if (!strcmp (argv[i], "--use-cadical"))
        {
          /* Implies '--no-clone' because not sure whether cadical's
             copy function has the same semantics as lingeling's clone
             function */
          use_cadical = 1;
          noclone = 1;
          fprintf (stderr, "Note: using CaDiCaL, which implies '--no-clone'.\n");
        }
      else if (argv[i][0] == '-')
	die ("invalid command line option '%s'", argv[i]);
      else if (isnumstr (argv[i]))
	maxk = atoi (argv[i]);
      else if (iname)
	die ("two files specified '%s' and '%s'", iname, argv[i]);
      else
	iname = argv[i];
    }

  if (verbose)
    {
      if (!use_cadical)
        lglbnr ("BLIMC Bounded Lingeling Model Checker", "c [blimc] ", msgfile);
      else
        msg (1, "BLIMC Bounded Lingeling Model Checker", msgfile);
    }
  setsighandlers ();

  msg (1, "reading %s", iname ? iname : "<stdin>");

  model = aiger_init ();

  if (iname)
    err = aiger_open_and_read_from_file (model, iname);
  else
    err = aiger_read_from_file (model, stdin);

  if (err)
    die ("parse error in '%s' at %s", iname ? iname : "<stdin>", err);

  msg (1, "MILOA %u %u %u %u %u",
       model->maxvar,
       model->num_inputs,
       model->num_latches, model->num_outputs, model->num_ands);

  msg (1, "BCJK %u %u %u %u %u",
       model->num_bad,
       model->num_constraints, model->num_justice, model->num_fairness);

  if (!model->num_outputs && !model->num_bad)
    die ("model contains no output nor bad state property");

  if (model->num_bad > 1)
    die ("can not handle multiple bad state properties");

  if (!model->num_bad && model->num_outputs > 1)
    die ("can not handle multiple outputs (without bad state property)");

  if (model->num_constraints > 0)
    die ("can not handle environment constraints");

  if (model->num_justice)
    msg (1, "ignoring %d justice properties", model->num_justice);

  if (model->num_fairness)
    msg (1, "ignoring %d fairness constraints", model->num_fairness);

  if (model->num_bad)
    num_bad = model->num_bad, badsyms = model->bad;
  else
    num_bad = model->num_outputs, badsyms = model->outputs;
  assert (num_bad == 1);

  init0 = init1 = initx = 0;
  for (j = 0; j < model->num_latches; j++)
    {
      unsigned rst = aigreset (j);
      if (rst == aiger_false)
	init0++;
      if (rst == aiger_true)
	init1++;
      if (rst == aiglatch (j))
	initx++;
    }

  if (model->num_latches)
    {
      msg (1, "%u latches initialized to 0", init0);
      msg (1, "%u latches initialized to 1", init1);
      msg (1, "%u latches uninitialized", initx);
    }
  else
    msg (1, "no latches, so purely combinational");

  coibytes = (model->maxvar + 1) * sizeof *coi;
  coi = new (0, coibytes);
  memset (coi, 0, coibytes);
  travcoi ();

  if (!use_cadical)
    {
      newlgl (0);
      lglsetprefix (lgl, "c [lglopt] ");
    }
  else
    {
      assert (!cadical);
      cadical = ccadical_init ();
      cadical_extracting_clauses = 1;
    }
  
  logic ();

  if (!use_cadical)
    prepfreeze ();

  msg (1, "encoded");

  if (!use_cadical)
    (void) lglsimp (lgl, opt);
  else
    ccadical_simplify (cadical);

  msg (1, "simplified");
  
  if ((!use_cadical && lglfixed (lgl, prepbad (0)) < 0) ||
      (use_cadical && ccadical_fixed (cadical, prepbad (0)) < 0))
    {
      res = 20;
      fprintf (outfile, "0\nb0\n.\n");
    }
  else
    {
      res = 0;
      if (!use_cadical)
        {
          lgltravall (lgl, 0, extract);
          msg (1, "extracted");
          if (verbose >= 1)
            lglstats (lgl);
          tmp = lgl, lgl = 0;
          lglrelease (tmp);
          newlgl (1);
          lglsetopt (lgl, "flipping", 0);
          lglsetopt (lgl, "boost", 0);
          lglsetopt (lgl, "simpdelay", 100);
          lglsetprefix (lgl, "c [lgl0] ");
        }
      else
        {
          cadical_extracting_clauses = 0;
          if (verbose >= 1)
            ccadical_print_statistics (cadical);
        }
      
      init ();
      msg (1, "maxk %d", maxk);

      /* Main BMC loop. */
      for (k = 0; k <= maxk; k++)
	{          
	  msg (1, "bound %d", k);
          
	  sprintf (prefix, "c [lgl%d] ", k);
          if (!use_cadical)
            lglsetprefix (lgl, prefix);
          
	  shiftcnf (k);
	  bad (lgl, k);
          
	  if (!noclone)
            {
              assert (!use_cadical);
              lglsetopt (lgl, "clim", 1000);
            }

          //DEBUG
          int debuglit;
          for (debuglit = 1; debuglit <= 8; debuglit++)
            fprintf(stderr, "DEBUG before sat-call bound %d---lit %d fixed? %d \n", k, debuglit, use_cadical ? ccadical_fixed (cadical, debuglit) : lglfixed (lgl, debuglit));
          
          if (!use_cadical)
            res = lglsat (lgl);
          else
            res = ccadical_solve (cadical);

          //DEBUG
          for (debuglit = 1; debuglit <= 8; debuglit++)
            fprintf(stderr, "DEBUG after sat-call bound %d---lit %d fixed? %d \n", k, debuglit, use_cadical ? ccadical_fixed (cadical, debuglit) : lglfixed (lgl, debuglit));

          
	  if (!res)
	    {
              assert (!use_cadical);
	      assert (!clone);
	      assert (!noclone);
	      clone = lglclone (lgl);
	      sprintf (prefix, "c [lgl%dclone%d] ", k, cloned++);
	      lglsetprefix (clone, prefix);
	      lglfixate (clone);
	      lglmeltall (clone);
#if 0
	      if (cloned & (cloned - 1))
		res = 0;
	      else
#endif
		res = lglsimp (clone, 1);
	      if (!res)
		{
		  lglsetopt (clone, "clim", -1);
		  res = lglsat (clone);
		  assert (res == 10 || res == 20);
		}
	      if (verbose >= 3)
		lglstats (clone);
	      tmp = clone, clone = 0;
#ifndef NDEBUG
	      fres =
#endif
		lglunclone (lgl, tmp);
	      assert (fres == res);
	      lglrelease (tmp);
	    }
	  assert (res);

	  if (res == 10)
	    break;

          //DEBUG: assumptions must be reset with second call of solver
          if (use_cadical)
            assert (ccadical_solve (cadical) == 10);
          else
            assert (lglsat (lgl) == 10);
              
	  assert (res == 20);
	  printf ("u%d\n", k);
	  fflush (stdout);
          
	  if (!model->num_latches)
	    break;
          
	  if (k < maxk && !((k + 1) & k))
            {
              if (!use_cadical)
                (void) lglsimp (lgl, 0);
              else
                ccadical_simplify (cadical);
            }
	}
      
      /* End of main BMC loop. */

      if (res == 10)
	{
	  fprintf (outfile, "1\nb0\n");
	  if (!nowitness)
	    {
	      for (i = 0; i < (int) model->num_latches; i++)
		{
		  if (ulitincoi (aiglatch (i)))
		    {
		      lit = shift (mainilit (aiglatch (i)), 0);
                      if (!use_cadical)
                        val = lglderef (lgl, lit);
                      else
                        val = ccadical_val (cadical, lit);
		    }
		  else
		    val = 0;
		  if (val > 0)
		    vch = '1';
		  else if (!val && xstim)
		    vch = 'x';
		  else
		    vch = '0';
		  fputc (vch, stdout);
		}
	      fputc ('\n', stdout);
	      for (i = 0; i <= k; i++)
		{
		  for (j = 0; j < model->num_inputs; j++)
		    {
		      if (ulitincoi (aiginput (j)))
			{
			  lit = shift (mainilit (aiginput (j)), i);
                          if (!use_cadical)
                            val = lglderef (lgl, lit);
                          else
                            val = ccadical_val (cadical, lit);
			}
		      else
			val = 0;
		      if (val > 0)
			vch = '1';
		      else if (!val && xstim)
			vch = 'x';
		      else
			vch = '0';
		      fputc (vch, stdout);
		    }
		  fputc ('\n', stdout);
		}
	    }
	  printf (".\n");
	}
      else if (res == 20 && !model->num_latches)
	fprintf (outfile, "0\nb0\n.\n");
      else
	fprintf (outfile, "2\nb0\n.\n");
      del (0, litmap, (model->maxvar + 2) * sizeof *litmap);
    }
  
  fflush (outfile);

  del (0, coi, (model->maxvar + 1) * sizeof *coi);

  aiger_reset (model);

  for (i = 0; i < nclauses; i++)
    del (0, clauses[i].lits,
	 (length (clauses[i].lits) + 1) * sizeof *clauses[i].lits);

  del (0, clauses, szclauses * sizeof *clauses);
  del (0, lits, szlits * sizeof *lits);

  resetsighandlers ();

  stats ();

  if (use_cadical)
    ccadical_release (cadical);
  else
    lglrelease (lgl);

  if (apitrace)
    fflush (apitrace), fclose (apitrace);

  msg (1, "exit %d", res);

  return res;
}
