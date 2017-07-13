/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>
#include <signal.h>
#include <unistd.h>

#include "mtl/Sort.h"
#include "core/Solver.h"
#ifdef GLUCOSE3
#include "core/Constants.h"
#include "utils/System.h"
#endif
#include "propagators/Propagator.h"

using namespace Minisat;

#ifdef BIN_DRUP
int Solver::buf_len = 0;
unsigned char Solver::drup_buf[2 * 1024 * 1024];
unsigned char* Solver::buf_ptr = drup_buf;
#endif

#define DONT_SHOW_PROPAGATIONS

//=================================================================================================
// Options:


static const char* _cat = "CORE";
static const char* _model = "Model";
static const char* _propagators = "Propagators";
#ifdef GLUCOSE3
static const char* _core_glucose3 = "CORE -- Glucose 3.0";

static DoubleOption  opt_K                  (_core_glucose3, "K",           "The constant used to force restart",            0.8,     DoubleRange(0, false, 1, false));           
static DoubleOption  opt_R                  (_core_glucose3, "R",           "The constant used to block restart",            1.4,     DoubleRange(1, false, 5, false));           
static IntOption     opt_size_lbd_queue     (_core_glucose3, "szLBDQueue",      "The size of moving average for LBD (restarts)", 50, IntRange(10, INT32_MAX));
static IntOption     opt_size_trail_queue   (_core_glucose3, "szTrailQueue",      "The size of moving average for trail (block restarts)", 5000, IntRange(10, INT32_MAX));
static IntOption     opt_first_reduce_db    (_core_glucose3, "firstReduceDB",      "The number of conflicts before the first reduce DB", 2000, IntRange(0, INT32_MAX));
static IntOption     opt_inc_reduce_db      (_core_glucose3, "incReduceDB",      "Increment for reduce DB", 300, IntRange(0, INT32_MAX));
static IntOption     opt_spec_inc_reduce_db (_core_glucose3, "specialIncReduceDB",      "Special increment for reduce DB", 1000, IntRange(0, INT32_MAX));
static IntOption     opt_lb_lbd_frozen_clause(_core_glucose3,"minLBDFrozenClause",        "Protect clauses if their LBD decrease and is lower than (for one turn)", 30, IntRange(0, INT32_MAX));
static IntOption     opt_lb_size_minimzing_clause(_core_glucose3, "minSizeMinimizingClause",      "The min size required to minimize clause", 30, IntRange(3, INT32_MAX));
static IntOption     opt_lb_lbd_minimzing_clause(_core_glucose3, "minLBDMinimizingClause",      "The min LBD required to minimize clause", 6, IntRange(3, INT32_MAX));
#else
static DoubleOption  opt_step_size          (_cat, "step-size",   "Initial step size",                             0.40,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_step_size_dec      (_cat, "step-size-dec","Step size decrement",                          0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_min_step_size      (_cat, "min-step-size","Minimal step size",                            0.06,     DoubleRange(0, false, 1, false));
#endif

static DoubleOption  opt_var_decay          (_cat, "var-decay",   "The variable activity decay factor",            0.80,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay       (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq    (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed        (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode         (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving       (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act       (_cat, "rnd-init",    "Randomize the initial activity", false);
#ifndef GLUCOSE3
static IntOption     opt_restart_first      (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc        (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
#endif
static DoubleOption  opt_garbage_frac       (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));

static IntOption     opt_printing_method    (_model, "out-format", "Method to print models (0=SAT, 1=ASP)", 0, IntRange(0, 1));
static BoolOption    opt_show_external_vars (_model, "ext-vars", "Show external variables", true);

static BoolOption    opt_heavy_propagation  (_propagators, "heavy-prop",    "Propagators perform heavy propagations", true);
static BoolOption    opt_lazy_propagation   (_propagators, "lazy-prop",     "At most one propagation performed", true);
static BoolOption    opt_early_propagation  (_propagators, "early-prop",    "Propagate as early as possible", true);
static IntOption     opt_min_conflict_tries (_propagators, "max-confl-try", "Maximum number of times an internal solver is called to in order to minimize a conflict", 1, IntRange(1, INT32_MAX));

//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
		verbosity         (0)
#ifdef GLUCOSE3
	, showModel         (0)
	, K                 (opt_K)
	, R                 (opt_R)
	, sizeLBDQueue      (opt_size_lbd_queue)
	, sizeTrailQueue    (opt_size_trail_queue)
	, firstReduceDB     (opt_first_reduce_db)
	, incReduceDB       (opt_inc_reduce_db)
	, specialIncReduceDB(opt_spec_inc_reduce_db)
	, lbLBDFrozenClause (opt_lb_lbd_frozen_clause)
	, lbSizeMinimizingClause(opt_lb_size_minimzing_clause)
	, lbLBDMinimizingClause(opt_lb_lbd_minimzing_clause)
#else
	, step_size         (opt_step_size)
  , step_size_dec     (opt_step_size_dec)
  , min_step_size     (opt_min_step_size)
  , timer             (5000)
#endif
	, var_decay         (opt_var_decay)
  , clause_decay      (opt_clause_decay)
  , random_var_freq   (opt_random_var_freq)
  , random_seed       (opt_random_seed)
#ifndef GLUCOSE3
  , VSIDS             (false)
#endif
	, heavy_propagation (opt_heavy_propagation)
  , lazy_propagation  (opt_lazy_propagation)
  , early_propagation (opt_early_propagation)
  , min_conflict_tries(opt_min_conflict_tries)
  , ccmin_mode        (opt_ccmin_mode)
  , phase_saving      (opt_phase_saving)
  , rnd_pol           (false)
  , rnd_init_act      (opt_rnd_init_act)
  , garbage_frac      (opt_garbage_frac)
#ifndef GLUCOSE3
  , restart_first     (opt_restart_first)
  , restart_inc       (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)
#endif

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
#ifdef GLUCOSE3
  , nbRemovedClauses(0), nbReducedClauses(0), nbDL2(0), nbBin(0), nbUn(0) , nbReduceDB(0)
  , conflictsRestarts(0), nbstopsrestarts(0), nbstopsrestartssame(0), lastblockatrestart(0)
  , curRestart(1)
#else
	, conflicts_VSIDS(0)
#endif
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches_bin        (WatcherDeleted(ca))
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
#ifndef GLUCOSE3
	, order_heap_CHB     (VarOrderLt(activity_CHB
#ifdef VAR_PRIORITY_ENABLED
                                   , priority
#endif
                       ))
#endif
  , order_heap_VSIDS   (VarOrderLt(activity_VSIDS
#ifdef VAR_PRIORITY_ENABLED
                                   , priority
#endif
                       ))
  , progress_estimate  (0)
  , remove_satisfied   (true)

#ifndef GLUCOSE3
  , core_lbd_cut       (3)
  , global_lbd_sum     (0)
  , lbd_queue          (50)
  , next_T2_reduce     (10000)
  , next_L_reduce      (15000)
  
  , counter            (0)
#endif

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)

    // Model printing options:
  , modelPrintingMethod(opt_printing_method)
  , showExternalVariables(opt_show_external_vars)
{
#ifdef GLUCOSE3
	lbdQueue.initSize(sizeLBDQueue);
	trailQueue.initSize(sizeTrailQueue);
	sumLBD = 0;
	nbclausesbeforereduce = firstReduceDB;
#endif
}

Solver::Solver(Solver *from) :

    // Parameters (user settable):
    //
		verbosity         (from->verbosity)
#ifdef GLUCOSE3
	, showModel         (from->showModel)
	, K                 (from->K)
	, R                 (from->R)
	, sizeLBDQueue      (from->sizeLBDQueue)
	, sizeTrailQueue    (from->sizeTrailQueue)
	, firstReduceDB     (from->firstReduceDB)
	, incReduceDB       (from->incReduceDB)
	, specialIncReduceDB(from->specialIncReduceDB)
	, lbLBDFrozenClause (from->lbLBDFrozenClause)
	, lbSizeMinimizingClause(from->lbSizeMinimizingClause)
	, lbLBDMinimizingClause(from->lbLBDMinimizingClause)
#else
  , step_size         (from->step_size)
  , step_size_dec     (from->step_size_dec)
  , min_step_size     (from->min_step_size)
  , timer             (from->timer)
#endif
  , var_decay         (from->var_decay)
  , clause_decay      (from->clause_decay)
  , random_var_freq   (from->random_var_freq)
  , random_seed       (from->random_seed)
#ifndef GLUCOSE3
  , VSIDS             (from->VSIDS)
#endif
  , heavy_propagation (from->heavy_propagation)
  , lazy_propagation  (from->lazy_propagation)
  , early_propagation (from->early_propagation)
  , min_conflict_tries(from->min_conflict_tries)
  , ccmin_mode        (from->ccmin_mode)
  , phase_saving      (from->phase_saving)
  , rnd_pol           (from->rnd_pol)
  , rnd_init_act      (from->rnd_init_act)
  , garbage_frac      (from->garbage_frac)
#ifndef GLUCOSE3
  , restart_first     (from->restart_first)
  , restart_inc       (from->restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor(from->learntsize_factor), learntsize_inc(from->learntsize_inc)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (from->learntsize_adjust_start_confl)
  , learntsize_adjust_inc         (from->learntsize_adjust_inc)
#endif

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
#ifdef GLUCOSE3
  , nbRemovedClauses(0), nbReducedClauses(0), nbDL2(0), nbBin(0), nbUn(0) , nbReduceDB(0)
  , conflictsRestarts(0), nbstopsrestarts(0), nbstopsrestartssame(0), lastblockatrestart(0)
  , curRestart(1)
#else
	, conflicts_VSIDS(0)
#endif
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , ok                 (from->ok)
  , cla_inc            (from->cla_inc)
  , var_inc            (from->var_inc)
  , watches_bin        (WatcherDeleted(ca))
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
#ifndef GLUCOSE3
  , order_heap_CHB     (VarOrderLt(activity_CHB
#ifdef VAR_PRIORITY_ENABLED
                                   , priority
#endif
                       ))
#endif
  , order_heap_VSIDS   (VarOrderLt(activity_VSIDS
#ifdef VAR_PRIORITY_ENABLED
                                   , priority
#endif
                       ))
  , progress_estimate  (from->progress_estimate)
  , remove_satisfied   (from->remove_satisfied)

#ifndef GLUCOSE3
  , core_lbd_cut       (from->core_lbd_cut)
  , global_lbd_sum     (from->global_lbd_sum)
  , lbd_queue          (from->lbd_queue.capacity())
  , next_T2_reduce     (from->next_T2_reduce)
  , next_L_reduce      (from->next_L_reduce)
  
  , counter            (from->counter)
#endif

    // Resource constraints:
    //
  , conflict_budget    (from->conflict_budget)
  , propagation_budget (from->propagation_budget)
  , asynch_interrupt   (false)

    // Model printing options:
  , modelPrintingMethod(from->modelPrintingMethod)
  , showExternalVariables(from->showExternalVariables)

{
#ifdef GLUCOSE3
	lbdQueue.initSize(sizeLBDQueue);
	trailQueue.initSize(sizeTrailQueue);
	sumLBD = 0;
	nbclausesbeforereduce = firstReduceDB;
#endif

	while (nVars() < from->nVars())
		newVar();
	for (auto it = from->propagators.cbegin(); it != from->propagators.cend(); it++)
		propagators.push_back((*it)->copy(this));
	variableNames = from->variableNames;
	// TODO: Should I also copy clauses/variables?
}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
	  watches_bin.init(mkLit(v, false));
    watches_bin.init(mkLit(v, true ));
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    activity_VSIDS.push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
#ifndef GLUCOSE3
    activity_CHB  .push(0);

    picked.push(0);
    conflicted.push(0);
    almost_conflicted.push(0);
#ifdef ANTI_EXPLORATION
    canceled.push(0);
#endif
#endif

#ifdef VAR_PRIORITY_ENABLED
    priority .push(0);
#endif
#ifdef VAR_FACTOR_ENABLED
    factors  .push(1);
#endif
    seen     .push(0);
#ifdef GLUCOSE3
    permDiff .push(0);
#else
    seen2    .push(0);
#endif
    polarity .push(sign);
    userDefPolarity.push(l_Undef);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}

bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;

    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
#ifdef SHOW_PROPAGATIONS
				printf("unit clause "); printLiteral(stdout, ps[0]); printf(" found\n");
#endif
				uncheckedEnqueue(ps[0]);
        vec<Lit> assumptions;
        return ok = (propagate(false) == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = c.size() == 2 ? watches_bin : watches;
    ws[~c[0]].push(Watcher(cr, c[1]));
    ws[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = c.size() == 2 ? watches_bin : watches;
    
    if (strict){
        remove(ws[~c[0]], Watcher(cr, c[1]));
        remove(ws[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        ws.smudge(~c[0]);
        ws.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];

    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)){
        Lit implied = c.size() != 2 ? c[0] : (value(c[0]) == l_True ? c[0] : c[1]);
        vardata[var(implied)].reason = CRef_Undef; }
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }

#ifdef GLUCOSE3
/************************************************************
 * Compute LBD functions
 *************************************************************/

inline int Solver::computeLBD(const vec<Lit> & lits,int end) {
	int nblevels = 0;
	MYFLAG++;

	for(int i=0;i<lits.size();i++) {
		int l = level(var(lits[i]));
		if (permDiff[l] != MYFLAG) {
			permDiff[l] = MYFLAG;
			nblevels++;
		}
	}

	return nblevels;
}

inline int Solver::computeLBD(const Clause &c) {
	int nblevels = 0;
	MYFLAG++;

	for(int i=0;i<c.size();i++) {
		int l = level(var(c[i]));
		if (permDiff[l] != MYFLAG) {
			permDiff[l] = MYFLAG;
			nblevels++;
		}
	}

	return nblevels;
}

/******************************************************************
 * Minimisation with binary reolution
 ******************************************************************/
void Solver::minimisationWithBinaryResolution(vec<Lit> &out_learnt) {
  
  // Find the LBD measure                                                                                                         
  int lbd = computeLBD(out_learnt);
  Lit p = ~out_learnt[0];
  
  if(lbd<=lbLBDMinimizingClause){
    MYFLAG++;
    
    for(int i = 1;i<out_learnt.size();i++) {
      permDiff[var(out_learnt[i])] = MYFLAG;
    }

    vec<Watcher>&  wbin  = watches_bin[p];
    int nb = 0;
    for(int k = 0;k<wbin.size();k++) {
      Lit imp = wbin[k].blocker;
      if(permDiff[var(imp)]==MYFLAG && value(imp)==l_True) {
	nb++;
	permDiff[var(imp)]= MYFLAG-1;
      }
      }
    int l = out_learnt.size()-1;
    if(nb>0) {
      nbReducedClauses++;
      for(int i = 1;i<out_learnt.size()-nb;i++) {
	if(permDiff[var(out_learnt[i])]!=MYFLAG) {
	  Lit p = out_learnt[l];
	  out_learnt[l] = out_learnt[i];
	  out_learnt[i] = p;
	  l--;i--;
	}
      }
      
      out_learnt.shrink(nb);
      
    }
  }
}
#endif

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
				// Shahab: revert propagators to the indicated level
				for (auto it = propagators.begin(); it != propagators.end(); it++)
						(*it)->backjump(level);
				// Shahab: and then continue with normal backjumping
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);

#ifndef GLUCOSE3
            if (!VSIDS){
                uint32_t age = conflicts - picked[x];
                if (age > 0){
                    double adjusted_reward = ((double) (conflicted[x] + almost_conflicted[x])) / ((double) age);
                    double old_activity = activity_CHB[x];
                    activity_CHB[x] = step_size * adjusted_reward + ((1 - step_size) * old_activity);
                    if (order_heap_CHB.inHeap(x)){
                        if (activity_CHB[x] > old_activity)
                            order_heap_CHB.decrease(x);
                        else
                            order_heap_CHB.increase(x);
                    }
                }
#ifdef ANTI_EXPLORATION
                canceled[x] = conflicts;
#endif
            }
#endif

            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;
#ifdef GLUCOSE3
    Heap<VarOrderLt>& order_heap = order_heap_VSIDS;
#else
    Heap<VarOrderLt>& order_heap = VSIDS ? order_heap_VSIDS : order_heap_CHB;
#endif

#ifdef GLUCOSE3
    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }
#endif

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty())
            return lit_Undef;
        else{
#ifndef GLUCOSE3
#ifdef ANTI_EXPLORATION
            if (!VSIDS){
                Var v = order_heap_CHB[0];
                uint32_t age = conflicts - canceled[v];
                while (age > 0){
                    double decay = pow(0.95, age);
                    activity_CHB[v] *= decay;
                    if (order_heap_CHB.inHeap(v))
                        order_heap_CHB.increase(v);
                    canceled[v] = conflicts;
                    v = order_heap_CHB[0];
                    age = conflicts - canceled[v];
                }
            }
#endif
#endif
            next = order_heap.removeMin();
        }

    return mkLit(next, (userDefPolarity[next] == l_Undef) ? (rnd_pol ? drand(random_seed) < 0.5 : polarity[next]) : (userDefPolarity[next] == l_False));
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int &out_lbd)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        // For binary clauses, we don't rearrange literals in propagate(), so check and make sure the first is an implied lit.
        if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

#ifdef GLUCOSE3
			if (c.learnt())
				claBumpActivity(c);

#ifdef DYNAMICNBLEVEL
			// DYNAMIC NBLEVEL trick (see competition'09 companion paper)
			if(c.learnt()  && c.lbd()>2) {
				int nblevels = computeLBD(c);
				if(nblevels+1<c.lbd() ) { // improve the LBD
					if(c.lbd()<=lbLBDFrozenClause) {
						c.removable(false);
					}
					// seems to be interesting : keep it for the next round
					c.set_lbd(nblevels); // Update it
				}
			}
#endif
#else
        // Update LBD if improved.
        if (c.learnt() && c.mark() != CORE){
            int lbd = computeLBD(c);
            if (lbd < c.lbd()){
                if (c.lbd() <= 30) c.removable(false); // Protect once from reduction.
                c.set_lbd(lbd);
                if (lbd <= core_lbd_cut){
                    learnts_core.push(confl);
                    c.mark(CORE);
                }else if (lbd <= 6 && c.mark() == LOCAL){
                    // Bug: 'cr' may already be in 'learnts_tier2', e.g., if 'cr' was demoted from TIER2
                    // to LOCAL previously and if that 'cr' is not cleaned from 'learnts_tier2' yet.
                    learnts_tier2.push(confl);
                    c.mark(TIER2); }
            }

            if (c.mark() == TIER2)
                c.touched() = conflicts;
            else if (c.mark() == LOCAL)
                claBumpActivity(c);
        }
#endif

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
#ifdef GLUCOSE3
							varBumpActivity(var(q));
							seen[var(q)] = 1;
							if (level(var(q)) >= decisionLevel()) {
								pathC++;
#ifdef UPDATEVARACTIVITY
								// UPDATEVARACTIVITY trick (see competition'09 companion paper)
								if ((reason(var(q))!= CRef_Undef)  && ca[reason(var(q))].learnt())
									lastDecisionLevel.push(q);
#endif
							}
							else out_learnt.push(q);
#else
                if (VSIDS){
                    varBumpActivity(var(q), .5);
                    add_tmp.push(q);
                }else
                    conflicted[var(q)]++;
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()){
                    pathC++;
								}else
                    out_learnt.push(q);
#endif
            }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;

    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = (c.size() == 2) ? 0 : 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

#ifdef GLUCOSE3
    /* ***************************************
      Minimisation with binary clauses of the asserting clause
      First of all : we look for small clauses
      Then, we reduce clauses with small LBD.
      Otherwise, this can be useless
     */
    if(out_learnt.size()<=lbSizeMinimizingClause) {
      minimisationWithBinaryResolution(out_learnt);
    }
#else
    out_lbd = computeLBD(out_learnt);
    if (out_lbd <= 6 && out_learnt.size() <= 30) // Try further minimization?
        if (binResMinimize(out_learnt))
            out_lbd = computeLBD(out_learnt); // Recompute LBD if minimized.
#endif

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

#ifdef GLUCOSE3
    // Compute LBD
    out_lbd = computeLBD(out_learnt,out_learnt.size());
  
#ifdef UPDATEVARACTIVITY
    // UPDATEVARACTIVITY trick (see competition'09 companion paper)
    if(lastDecisionLevel.size()>0) {
      for(int i = 0;i<lastDecisionLevel.size();i++) {
        if(ca[reason(var(lastDecisionLevel[i]))].lbd()<out_lbd)
          varBumpActivity(var(lastDecisionLevel[i]));
      }
      lastDecisionLevel.clear();
    }
#endif	    
#else
    if (VSIDS){
        for (int i = 0; i < add_tmp.size(); i++){
            Var v = var(add_tmp[i]);
            if (level(v) >= out_btlevel - 1)
                varBumpActivity(v, 1);
        }
        add_tmp.clear();
    }else{
        seen[var(p)] = true;
        for(int i = out_learnt.size() - 1; i >= 0; i--){
            Var v = var(out_learnt[i]);
            CRef rea = reason(v);
            if (rea != CRef_Undef){
                const Clause& reaC = ca[rea];
                for (int i = 0; i < reaC.size(); i++){
                    Lit l = reaC[i];
                    if (!seen[var(l)]){
                        seen[var(l)] = true;
                        almost_conflicted[var(l)]++;
                        analyze_toclear.push(l); } } } } }
#endif

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}

#ifndef GLUCOSE3
// Try further learnt clause minimization by means of binary clause resolution.
bool Solver::binResMinimize(vec<Lit>& out_learnt)
{
    // Preparation: remember which false variables we have in 'out_learnt'.
    counter++;
    for (int i = 1; i < out_learnt.size(); i++)
        seen2[var(out_learnt[i])] = counter;

    // Get the list of binary clauses containing 'out_learnt[0]'.
    const vec<Watcher>& ws = watches_bin[~out_learnt[0]];

    int to_remove = 0;
    for (int i = 0; i < ws.size(); i++){
        Lit the_other = ws[i].blocker;
        // Does 'the_other' appear negatively in 'out_learnt'?
        if (seen2[var(the_other)] == counter && value(the_other) == l_True){
            to_remove++;
            seen2[var(the_other)] = counter - 1; // Remember to remove this variable.
        }
    }

    // Shrink.
    if (to_remove > 0){
        int last = out_learnt.size() - 1;
        for (int i = 1; i < out_learnt.size() - to_remove; i++)
            if (seen2[var(out_learnt[i])] != counter)
                out_learnt[i--] = out_learnt[last--];
        out_learnt.shrink(to_remove);
    }
    return to_remove != 0;
}
#endif

// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

        // Special handling for binary clauses like in 'analyze()'.
        if (c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = (c.size() == 2) ? 0 : 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    Var x = var(p);
#ifndef GLUCOSE3
    if (!VSIDS){
        picked[x] = conflicts;
        conflicted[x] = 0;
        almost_conflicted[x] = 0;
#ifdef ANTI_EXPLORATION
        uint32_t age = conflicts - canceled[var(p)];
        if (age > 0){
            double decay = pow(0.95, age);
            activity_CHB[var(p)] *= decay;
            if (order_heap_CHB.inHeap(var(p)))
                order_heap_CHB.increase(var(p));
        }
#endif
    }
#endif

    assigns[x] = lbool(!sign(p));
    vardata[x] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/

CRef Solver::propagate(bool applyExternals)
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();
    watches_bin.cleanAll();

	do
	{ // Shahab: the outer loop takes care of slower propagation mechanisms such as
		//         acyclicity and/or reachability while the inner loop takes care of
		//         faster propagations such as unit propagation.
    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        vec<Watcher>& ws_bin = watches_bin[p];  // Propagate binary clauses first.
        for (int k = 0; k < ws_bin.size(); k++){
            Lit the_other = ws_bin[k].blocker;
            if (value(the_other) == l_False)
                return ws_bin[k].cref;
            if(value(the_other) == l_Undef)
						{
#ifdef SHOW_PROPAGATIONS
								printf("propagating "); printLiteral(stdout, the_other); printf(" at decision level %d because of binary clause ", decisionLevel());
								printLiteral(stdout, the_other); printf(" "); printLiteral(stdout, ~p); printf("\n");
#endif
								uncheckedEnqueue(the_other, ws_bin[k].cref);
						}
        }

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
						{
#ifdef SHOW_PROPAGATIONS
								printf("propagating "); printLiteral(stdout, first); printf(" at decision level %d because of ", decisionLevel());
								for (int counter = 0; counter < c.size(); counter++)
								{
									printLiteral(stdout, c[counter]);
									printf(" ");
								}
								printf("\n");
#endif
                uncheckedEnqueue(first, cr);
						}

        NextClause:;
        }
        ws.shrink(i - j);
		}

/*		if (confl == CRef_Undef)
		{
			for (auto it = propagators.begin(); it != propagators.end(); it++)
				if ((*it)->propagate(p))
				{
					confl = (*it)->getConflictClause();
					qhead = trail.size();
					break;
				}
		}*/

		if ((confl == CRef_Undef) && ((trail.size() >= nVars()) || applyExternals))
		{
			for (auto it = propagators.begin(); it != propagators.end(); it++)
				if ((*it)->propagateAll())
				{
					confl = (*it)->getConflictClause();
					qhead = trail.size();
					break;
				}
		}
	}
	while (qhead < trail.size());
	
  propagations += num_props;
  simpDB_props -= num_props;

  return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
#ifdef GLUCOSE3
    bool operator () (CRef x, CRef y) { 
			// Main criteria... Like in MiniSat we keep all binary clauses
			if(ca[x].size()> 2 && ca[y].size()==2) return 1;

			if(ca[y].size()>2 && ca[x].size()==2) return 0;
			if(ca[x].size()==2 && ca[y].size()==2) return 0;

			// Second one  based on literal block distance
			if(ca[x].lbd()> ca[y].lbd()) return 1;
			if(ca[x].lbd()< ca[y].lbd()) return 0;

			// Finally we can use old activity or size, we choose the last one
			return ca[x].activity() < ca[y].activity();
			//return x->size() < y->size();

			//return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
    }    
#else
    bool operator () (CRef x, CRef y) const { return ca[x].activity() < ca[y].activity(); }
#endif
};
void Solver::reduceDB()
{
  int     i, j;
#ifdef GLUCOSE3
  nbReduceDB++;

  // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
  if(ca[learnts_local[learnts_local.size() / RATIOREMOVECLAUSES]].lbd()<=3) nbclausesbeforereduce +=specialIncReduceDB;
  // Useless :-)
  if(ca[learnts_local.last()].lbd()<=5) nbclausesbeforereduce +=specialIncReduceDB;
#endif
  sort(learnts_local, reduceDB_lt(ca));

  // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
  // Keep clauses which seem to be usefull (their lbd was reduce during this sequence)

  int limit = learnts_local.size() / 2;
  for (i = j = 0; i < learnts_local.size(); i++){
    Clause& c = ca[learnts_local[i]];
		bool test;
#ifdef GLUCOSE3
		test = (c.lbd() > 2) && (c.size() > 2) && c.removable() &&  !locked(c) && (i < limit);
#else
		test = c.removable() && !locked(c) && (i < limit);
#endif
#ifndef GLUCOSE3
		if (c.mark() == LOCAL)
#endif
	    if (test) {
		    removeClause(learnts_local[i]);
#ifdef GLUCOSE3
  		  nbRemovedClauses++;
#endif
	    }
		  else {
  		  if (!c.removable()) limit++; //we keep c, so we can delete an other clause
    		c.removable(true);       // At the next step, c can be delete
    		learnts_local[j++] = learnts_local[i];
  		}
  }
  learnts_local.shrink(i - j);

	checkGarbage();
}

#ifndef GLUCOSE3
void Solver::reduceDB_Tier2()
{
    int i, j;
    for (i = j = 0; i < learnts_tier2.size(); i++){
        Clause& c = ca[learnts_tier2[i]];
        if (c.mark() == TIER2)
            if (!locked(c) && c.touched() + 30000 < conflicts){
                learnts_local.push(learnts_tier2[i]);
                c.mark(LOCAL);
                //c.removable(true);
                c.activity() = 0;
                claBumpActivity(c);
            }else
                learnts_tier2[j++] = learnts_tier2[i];
    }
    learnts_tier2.shrink(i - j);
}
#endif

void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}

#ifndef GLUCOSE3
void Solver::safeRemoveSatisfied(vec<CRef>& cs, unsigned valid_mark)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (c.mark() == valid_mark)
            if (satisfied(c))
                removeClause(cs[i]);
            else
                cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}
#endif

void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);

#ifndef GLUCOSE3
    order_heap_CHB  .build(vs);
#endif
    order_heap_VSIDS.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    vec<Lit> assumptions;
    if (!ok || propagate(false) != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
#ifdef GLUCOSE3
    removeSatisfied(learnts_local);
#else
    removeSatisfied(learnts_core); // Should clean core first.
    safeRemoveSatisfied(learnts_tier2, TIER2);
    safeRemoveSatisfied(learnts_local, LOCAL);
#endif
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
#ifdef GLUCOSE3
lbool Solver::search(const vec<Lit> &assumptions, int nof_conflicts)
#else
lbool Solver::search(const vec<Lit> &assumptions, int &nof_conflicts)
#endif
{
	assert(ok);
	int         backtrack_level;
	vec<Lit>    learnt_clause;
#ifdef GLUCOSE3
	int         conflictC = 0;
	vec<Lit>    selectors;
	int         nblevels;
	bool blocked=false;
#else
	int         lbd;
	bool        cached = false;
#endif
	starts++;

	for (;;){
		CRef confl = propagate(early_propagation && (decisionLevel() >= assumptions.size()));
		if (confl != CRef_Undef){
			// CONFLICT
			conflicts++; nof_conflicts--;
#ifdef GLUCOSE3
			conflictC++; conflictsRestarts++;
			if(conflicts%5000==0 && var_decay<0.95)
				var_decay += 0.01;

			if (verbosity >= 1 && conflicts%verbEveryConflicts==0){
				printf("c | %8d   %7d    %5d | %7d %8d %8d | %5d %8d   %6d %8d | %6.3f %% |\n",
				       (int)starts,(int)nbstopsrestarts, (int)(conflicts/starts),
				       (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
				       (int)nbReduceDB, nLearnts(), (int)nbDL2,(int)nbRemovedClauses, progressEstimate()*100);
			}
#else
			if (VSIDS){
				if (--timer == 0 && var_decay < 0.95) timer = 5000, var_decay += 0.01;
			}
			else if (step_size > min_step_size) step_size -= step_size_dec;

			if (conflicts == 100000 && learnts_core.size() < 100) core_lbd_cut = 5;
#endif

			// Shahab: Using propagators, we might receive a conflict that does not belong to
			//         the current decision level (i.e., for all literals L in the conflict
			//         clause, decision_level(l) is less than current decision level). This
			//         causes problems to "analyze" procedure.
			//         Hence, we first backtrack to the maximum decision level of the conflict
			//         clause and then continue with the conflict analysis
			int maxDecLevel = 0;
			Clause &conflictClause = ca[confl];
			for (int i = 0; i < conflictClause.size(); i++)
				if (vardata[var(conflictClause[i])].level > maxDecLevel)
				{
					maxDecLevel = vardata[var(conflictClause[i])].level;
					if (maxDecLevel == decisionLevel())
						break; // already at maximum possible level. stop looking further.
				}
			if (maxDecLevel < decisionLevel())
				cancelUntil(maxDecLevel);
			// Shahab: then, continue with normal analysis

			if (decisionLevel() == 0) return l_False;
#ifdef GLUCOSE3
			trailQueue.push(trail.size());
			// BLOCK RESTART (CP 2012 paper)
			if( conflictsRestarts>LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid()  && trail.size()>R*trailQueue.getavg()) {
				lbdQueue.fastclear();
				nbstopsrestarts++;
				if(!blocked) {lastblockatrestart=starts;nbstopsrestartssame++;blocked=true;}
			}
#endif

			learnt_clause.clear();
#ifdef GLUCOSE3
			analyze(confl, learnt_clause, backtrack_level, nblevels);
			lbdQueue.push(nblevels);
			sumLBD += nblevels;
#else
			analyze(confl, learnt_clause, backtrack_level, lbd);
#endif
			cancelUntil(backtrack_level);

#ifndef GLUCOSE3
			lbd--;
			if (VSIDS){
				cached = false;
				conflicts_VSIDS++;
				lbd_queue.push(lbd);
				global_lbd_sum += (lbd > 50 ? 50 : lbd); }
#endif

			if (learnt_clause.size() == 1){
				uncheckedEnqueue(learnt_clause[0]);
#ifdef GLUCOSE3
				nbUn++;
#endif
			}else{
				CRef cr = ca.alloc(learnt_clause, true);
#ifdef GLUCOSE3
				ca[cr].set_lbd(nblevels);
				if(nblevels<=2) nbDL2++; // stats
				if(ca[cr].size()==2) nbBin++; // stats
				learnts_local.push(cr);
#else
				ca[cr].set_lbd(lbd);
				if (lbd <= core_lbd_cut){
					learnts_core.push(cr);
					ca[cr].mark(CORE);
				}else if (lbd <= 6){
					learnts_tier2.push(cr);
					ca[cr].mark(TIER2);
					ca[cr].touched() = conflicts;
				}else{
					learnts_local.push(cr);
					claBumpActivity(ca[cr]); }
#endif
				attachClause(cr);
#ifdef GLUCOSE3
				claBumpActivity(ca[cr]);
#endif
				uncheckedEnqueue(learnt_clause[0], cr);
			}

#ifdef GLUCOSE3
			varDecayActivity();
#else
			if (VSIDS) varDecayActivity();
#endif
			claDecayActivity();
		}else{
			// NO CONFLICT
#ifdef GLUCOSE3
			// Our dynamic restart, see the SAT09 competition compagnion paper
			if (lbdQueue.isvalid() && ((lbdQueue.getavg()*K*conflictsRestarts) > sumLBD)) {
				lbdQueue.fastclear();
				progress_estimate = progressEstimate();
				int bt = 0;
				cancelUntil(bt);
				return l_Undef; }
#else
			bool restart = false;
			if (!VSIDS)
				restart = nof_conflicts <= 0;
			else if (!cached){
				restart = lbd_queue.full() && (lbd_queue.avg() * 0.8 > global_lbd_sum / conflicts_VSIDS);
				cached = true;
			}
			if (restart/* || !withinBudget()*/){
				lbd_queue.clear();
				cached = false;
				// Reached bound on number of conflicts:
				progress_estimate = progressEstimate();
				cancelUntil(0);
				return l_Undef; }
#endif

			// Simplify the set of problem clauses:
			if (decisionLevel() == 0 && !simplify())
				return l_False;

#ifdef GLUCOSE3
			// Perform clause database reduction !
			if (conflicts >= curRestart * nbclausesbeforereduce)
			{
				assert(learnts_local.size()>0);
				curRestart = (conflicts/ nbclausesbeforereduce)+1;
				reduceDB();
				nbclausesbeforereduce += incReduceDB;
			}
#else
			if (conflicts >= next_T2_reduce){
				next_T2_reduce = conflicts + 10000;
				reduceDB_Tier2(); }
			if (conflicts >= next_L_reduce){
				next_L_reduce = conflicts + 15000;
				reduceDB(); }
#endif

			Lit next = lit_Undef;
			while (decisionLevel() < assumptions.size()){
				// Perform user provided assumption:
				Lit p = assumptions[decisionLevel()];
				if (value(p) == l_True){
					// Dummy decision level:
					// newDecisionLevel();
					// In Minisat, when an assumption is already deduced, i.e., value(p) is
					// true, a dummy decision level is created and nothing else happens but,
					// when propagators are present, such a dummy decision level means that
					// some of the propagators are not tested for consistency. If such a case
					// happens in the end of solving a program, it means that we might find a
					// model that is inconsistent with the propagators.
					//
					// So, when propagators are present, even dummy decision levels should
					// pass some consistency tests and, hence, the propagate() method should
					// run.
					next = p;
					break;
				}else if (value(p) == l_False){
					analyzeFinal(~p, conflict);
					return l_False;
				}else{
					next = p;
					break;
				}
			}

			if (next == lit_Undef) {
				// New variable decision:
				decisions++;
				next = pickBranchLit();
				//		printf("Setting literal %i,\n",var(next));
				if (next == lit_Undef) {
					// Model found:
					decisionLits.growTo(trail_lim.size());
					for (int i = 0; i < trail_lim.size(); i++)
						decisionLits[i] = trail[trail_lim[i]];
					return l_True;
				}
			}

			if(next != lit_Undef) {
				// Increase decision level and enqueue 'next'
				newDecisionLevel();
				if (value(next) != l_True)
					// Shahab: this check is needed so that dummy decision varibales
					// are not put in the queue twice
					uncheckedEnqueue(next);

#ifdef SHOW_PROPAGATIONS
				printf("deciding literal "); printLiteral(stdout, next); printf("\n");
#endif
			}
		}
	}
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

#ifndef GLUCOSE3
/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

static bool switch_mode = false;
static void SIGALRM_switch(int signum) { switch_mode = true; }
#endif

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_(const vec<Lit> &assumptions)
{
#ifndef GLUCOSE3
	signal(SIGALRM, SIGALRM_switch);
	alarm(2500);
#endif

	model.clear();
	decisionLits.clear();
	conflict.clear();
	rebuildOrderHeap();

	if (!ok) return l_False;
	// Initializing propagators:
	for (auto it = propagators.begin(); it != propagators.end(); it++)
		if (!((*it)->initialize()))
		{
			ok = false;
			break;
		}

	if (!ok) return l_False;
	solves++;

#ifndef GLUCOSE3
	max_learnts               = nClauses() * learntsize_factor;
	learntsize_adjust_confl   = learntsize_adjust_start_confl;
	learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
#endif
	lbool   status        = l_Undef;
	if(verbosity>=1) {
		printf("c ========================================[ MAGIC CONSTANTS ]==============================================\n");
		printf("c | Constants are supposed to work well together :-)                                                      |\n");
		printf("c | however, if you find better choices, please let us known...                                           |\n");
		printf("c |-------------------------------------------------------------------------------------------------------|\n");
		printf("c |                                |                                |                                     |\n"); 
		printf("c | - Restarts:                    | - Reduce Clause DB:            | - Minimize Asserting:               |\n");
#ifdef GLUCOSE3
		printf("c |   * LBD Queue    : %6d      |   * First     : %6" PRIu64 "         |    * size < %3d                     |\n",lbdQueue.maxSize(),nbclausesbeforereduce,lbSizeMinimizingClause);
		printf("c |   * Trail  Queue : %6d      |   * Inc       : %6d         |    * lbd  < %3d                     |\n",trailQueue.maxSize(),incReduceDB,lbLBDMinimizingClause);
		printf("c |   * K            : %6.2f      |   * Special   : %6d         |                                     |\n",K,specialIncReduceDB);
		printf("c |   * R            : %6.2f      |   * Protected :  (lbd)< %2d     |                                     |\n",R,lbLBDFrozenClause);
#endif
		printf("c |                                |                                |                                     |\n");
#ifdef GLUCOSE3
		printf("c ==================================[ Search Statistics (every %6d conflicts) ]=========================\n",verbEveryConflicts);
#else
		printf("c ===============================================[ Search Statistics ]=====================================\n");
#endif
		printf("c |                                                                                                       |\n"); 
		printf("c |          RESTARTS           |          ORIGINAL         |              LEARNT              | Progress |\n");
		printf("c |       NB   Blocked  Avg Cfc |    Vars  Clauses Literals |   Red   Learnts    LBD2  Removed |          |\n");
		printf("c =========================================================================================================\n");
	}

#ifndef GLUCOSE3
	add_tmp.clear();

	VSIDS = true;
	int init = 10000;
	while (status == l_Undef && init > 0)
		status = search(assumptions, init);
	VSIDS = false;
#endif
	// Search:
	int curr_restarts = 0;
	while (status == l_Undef){
#ifdef GLUCOSE3
		status = search(assumptions, 0); // the parameter is useless in glucose, kept to allow modifications

		if (!withinBudget()) break;
		curr_restarts++;
#else
		if (VSIDS){
			int weighted = INT32_MAX;
			status = search(assumptions, weighted);
		}else{
			int nof_conflicts = luby(restart_inc, curr_restarts) * restart_first;
			curr_restarts++;
			status = search(assumptions, nof_conflicts);
		}
		if (!VSIDS && switch_mode){
			VSIDS = true;
			if (verbosity >= 1)
			{
				printf("c Switched to VSIDS.\n");
				fflush(stdout);
			}
			picked.clear();
			conflicted.clear();
			almost_conflicted.clear();
#ifdef ANTI_EXPLORATION
			canceled.clear();
#endif
		}
#endif
	}

	if (verbosity >= 1)
		printf("c =========================================================================================================\n");

	if (status == l_True){
		// Extend & copy model:
		model.growTo(nVars());
		for (int i = 0; i < nVars(); i++) model[i] = value(i);
	}else if (status == l_False && conflict.size() == 0)
		ok = false;

	cancelUntil(0);

	return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumps.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumps.size(); i++){
        assert(value(assumps[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("c Wrote %d clauses with %d variables.\n", cnt, max);
}

void Solver::printLiteral(FILE *out, Lit l)
{
	fprintf(out, "%s", sign(l) ? "-" : "");

	Var v = var(l);
	if (modelPrintingMethod == 0)
		fprintf(out, "%d", v + 1);
	else
	{
		auto it = variableNames.find(v);
		if (it != variableNames.end())
			fprintf(out, "%s", it->second.c_str());
		else
			fprintf(out, "%d", v + 1);
	}
}

// Prints the satisfying model. Assumes that 'model' is not empty.
void Solver::printModel(FILE *out)
{
  assert(model.size() != 0);

	if (modelPrintingMethod == 1)
	{ // Print model in ASP way.
    fprintf(out, "ANSWER\n");
		for (auto it = variableNames.cbegin(); it != variableNames.cend(); it++)
			if (modelValue(it->first) == l_True)
			{
				if (showExternalVariables || (((it->second).size() > 0) && ((it->second)[0] != '_')))
          fprintf(out, "%s. ", it->second.c_str());
			}
    fprintf(out, "\n");
	}
	else
	{ // Print model in SAT way.
    fprintf(out, "v ");
    for (int i = 0; i < model.size(); i++)
    {
      if (model[i] == l_True)
        fprintf(out, "%d ", i + 1);
      else
        fprintf(out, "%d ", -(i + 1));
    }
    fprintf(out, "\n");
	}
}

//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    watches_bin.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            vec<Watcher>& ws_bin = watches_bin[p];
            for (int j = 0; j < ws_bin.size(); j++)
                ca.reloc(ws_bin[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
#ifdef GLUCOSE3
    for (int i = 0; i < learnts_local.size(); i++)
        ca.reloc(learnts_local[i], to);
#else
    for (int i = 0; i < learnts_core.size(); i++)
        ca.reloc(learnts_core[i], to);
    for (int i = 0; i < learnts_tier2.size(); i++)
        ca.reloc(learnts_tier2[i], to);
    for (int i = 0; i < learnts_local.size(); i++)
        ca.reloc(learnts_local[i], to);
#endif

    // All original:
    //
#ifdef GLUCOSE3
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
#else
    int i, j;
    for (i = j = 0; i < clauses.size(); i++)
        if (ca[clauses[i]].mark() != 1){
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i]; }
    clauses.shrink(i - j);
#endif
}

void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

