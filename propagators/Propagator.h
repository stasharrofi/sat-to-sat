#ifndef PROPAGATOR_H
#define PROPAGATOR_H

#include "core/SolverTypes.h"
#include "core/Solver.h"

#define noPROPAGATOR_DEBUG

using namespace Minisat;

class Propagator
{
	public:
		enum Effect { NO_EFFECT = 0, NORMAL_PROPAGATION = 1, DESTRUCTIVE_PROPAGATION = 2, CONFLICT = 3 };
	private:
		CRef ConflictClause;
	protected:
		Solver *SolverInstance;
		int propagationStartIndex;
#ifdef PROPAGATOR_DEBUG
		bool debuggingEnabled;
		const char *propagatorName;
#endif

		void setConflictClause(CRef &cc) { ConflictClause = cc; }

		/*
		 * Called to add a new clause to the database.
		 * Return value shows the following:
		 *   NO_EFFECT: Clause was not added because one of the following happened: (1) the
		 *     clause was already satisfied, (2) the clause contained at least two
		 *     unassigned literals, or (3) the clause had exactly one unassigned literal
		 *     but either the solver's heavy propagation flag was not set or both
		 *     lazyPropCompleted and solver's lazy propagation flag were set true.
		 *   NORMAL_PROPAGATION: Clause contained exactly one unassigned literal with all
		 *     other literals being false. So, the unassigned literal was propagated true.
		 *     Also, the backtracking level was the current decision level. Therefore, the
		 *     propagation could have been done in the current level and so the state is
		 *     intact.
		 *   DESTRUCTIVE_PROPAGATION: Clause contained exactly one unassigned literal with
		 *     all other literals being false. So, the unassigned literal was propagated
		 *     true. However, the backtracking level was before the current decision level
		 *     and, therefore, the state is no longer valid. Hence, the propagator should
		 *     abandon what it is doing and return the control to the solver.
		 *   CONFLICT: All literals in the clause were false causing a conflict.
		 */
		Effect addNewClause(vec<Lit> &clause, bool lazyPropCompleted);
		
		int getCurrentDecisionLevel() { return SolverInstance->decisionLevel(); }
		Lit getTrailLiteralAt(int position) { return SolverInstance->trail[position]; }
		int getTrailLimit(int level) { return (level == SolverInstance->decisionLevel()) ? SolverInstance->trail.size() : SolverInstance->trail_lim[level]; }

		virtual bool propagate(int start, int end); // Used to propagate many literals at once. literals that will be
																								// propagated are "trail[start] ... trail[end - 1]"
																								// Output is to be interpreted similar to "propagate(Lit p)"
		virtual bool propagate(Lit p) = 0;					// Returns true if some conflict was found.
																								// If conflict found, use "getConflictClause()" to retrieve it
		virtual void cancelUntil(int level);				// Backtracking for the theory to revert its internal data state
																								// default implementation for when no change to internal data needed
	public:
		Propagator(Solver *S);

		Solver *getSolver(void);
		CRef &getConflictClause(void);

		bool propagateAll(void);                    // Takes care of internal propagation start index and uses method
																								// propagate(start, end) to do the propagation.
																								// Output is to be interpreted similar to "propagate(Lit p)"
																								// Returns true if some conflict was found.
																								// If conflict found, use "getConflictClause()" to retrieve it
		void backjump(int level);										// Called when backjumping to some level; Everything in that level
																								// is kept but everything after that level is cancelled.
																								// This method takes care of internal propagation start index and
																								// calls "cancelUntil()" method so that the theory also backjumps.

		virtual bool initialize(void) = 0;					// Returns true if initialization successful.
																								// If unsuccessful, use "getConflictClause()" to get the conflict
		virtual const vec<Lit> &explain() = 0;			// Returns a subset S of the current model (interpretation) to explain
																								// why the propagator is satisfied. result set S means that whenever S
																								// is a subset of a (partial) interpretation I then I is guaranteed to
																								// satisfy the propagator. Should only be called when the solver
																								// containing current propagator has found a model
		virtual bool isTheoryVar(Var v) = 0;				// Used to guarantee that theory variables are not simplified by the
																								// simpSolver. Theory refers to the propagator's background theory.

		virtual Propagator *copy(Solver *S) = 0;
};

inline int ConvertVarToInt(Var v)
{
	return v+1;
}

inline int ConvertLiteralToInt(Lit p)
{
	bool s = sign(p);
	Var v = var(p);
	return (s ? -ConvertVarToInt(v) : ConvertVarToInt(v));
}

inline CRef &Propagator::getConflictClause()
{
	return ConflictClause;
}

inline Solver *Propagator::getSolver()
{
	return SolverInstance;
}
#endif
