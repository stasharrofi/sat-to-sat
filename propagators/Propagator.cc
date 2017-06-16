#include "Propagator.h"

#ifdef PROPAGATOR_DEBUG
#define noDEEP_PROPAGATOR_DEBUG
#endif

#ifdef PROPAGATOR_DEBUG
static const char *unnamedPropagatorName = "unnamed";
#endif

Propagator::Propagator(Solver *S)
{
	propagationStartIndex = 0;
	SolverInstance = S;
#ifdef PROPAGATOR_DEBUG
	debuggingEnabled = false;
	propagatorName = unnamedPropagatorName;
#endif
}

Propagator::Effect Propagator::addNewClause(vec<Lit> &clause, bool lazyPropCompleted)
{
#ifdef PROPAGATOR_DEBUG
	if (debuggingEnabled)
	{
		printf("propagator (%s): adding clause ", propagatorName);
		for (int i = 0; i < clause.size(); i++)
		{
			SolverInstance->printLiteral(stdout, clause[i]);
			printf(" ");
		}
		printf("\n");
	}
#endif

	int undefCount = 0;
	int maxLevel = -1, secondMaxLevel = -1;
	int maxLevelIndex = -1, secondMaxLevelIndex = -1;
	for (int i = 0; i < clause.size(); i++)
	{
		if (SolverInstance->value(clause[i]) == l_True)
			return NO_EFFECT;
		else if (SolverInstance->value(clause[i]) == l_Undef)
		{
			if (undefCount > 0)
				return NO_EFFECT;
			undefCount = 1;
			Lit tmp = clause[0];
			clause[0] = clause[i];
			clause[i] = tmp;
			if (maxLevelIndex == 0)
				maxLevelIndex = i;
			else if (secondMaxLevelIndex == 0)
				secondMaxLevelIndex = i;
		}
		else
		{
			int curLevel = SolverInstance->level(var(clause[i]));
			if (curLevel > maxLevel)
			{
				secondMaxLevelIndex = maxLevelIndex;
				secondMaxLevel = maxLevel;
				maxLevelIndex = i;
				maxLevel = curLevel;
			}
			else if (curLevel > secondMaxLevel)
			{
				secondMaxLevelIndex = i;
				secondMaxLevel = curLevel;
			}
		}
	}

	if ((undefCount > 0) && !(SolverInstance->heavy_propagation))
		return NO_EFFECT;
	if ((undefCount > 0) && lazyPropCompleted && SolverInstance->lazy_propagation)
		return NO_EFFECT;

	if (clause.size() > 1)
	{
		Lit tmp = clause[undefCount];
		clause[undefCount] = clause[maxLevelIndex];
		clause[maxLevelIndex] = tmp;

		if (undefCount == 0)
		{
			tmp = clause[1];
			clause[1] = clause[secondMaxLevelIndex];
			clause[secondMaxLevelIndex] = tmp;
		}
	}

	CRef cr = SolverInstance->ca.alloc(clause, true);
#ifdef DEEP_PROPAGATOR_DEBUG
	if (debuggingEnabled)
		printf("propagator (%s): added clause under CRef %d\n", propagatorName, cr);
#endif

	if (clause.size() >= 2)
	{
		SolverInstance->learnts_local.push(cr);
		SolverInstance->attachClause(cr);
		SolverInstance->claBumpActivity(SolverInstance->ca[cr]);
	}

	if (undefCount == 0)
	{
		ConflictClause = cr;
		return CONFLICT;
	}

	if (clause.size() == 1)
	{
#ifdef PROPAGATOR_DEBUG
		if (debuggingEnabled)
			printf("propagator (%s): reason size is 1 ==> call uncheckedEnqueue and exit\n", propagatorName);
#endif
		SolverInstance->cancelUntil(0);
		SolverInstance->uncheckedEnqueue(clause[0]);

		return DESTRUCTIVE_PROPAGATION;
	}

	if (SolverInstance->decisionLevel() > maxLevel)
	{
#ifdef PROPAGATOR_DEBUG
		if (debuggingEnabled)
			printf("propagator (%s): backtracking from level %d to level %d\n", propagatorName, SolverInstance->decisionLevel(), maxLevel);
#endif
		SolverInstance->cancelUntil(maxLevel); // backtrack to highest decision level in reason

		SolverInstance->uncheckedEnqueue(clause[0], cr);
		return DESTRUCTIVE_PROPAGATION;
	}
	else
	{
		SolverInstance->uncheckedEnqueue(clause[0], cr);
		return NORMAL_PROPAGATION;
	}
}

void Propagator::cancelUntil(int level)
{ // default implementation does nothing; override if necessary.
}

bool Propagator::propagate(int start, int end)
{
	for (int i = start; i < end; i++)
	{
		if (i >= SolverInstance->trail.size())
			return false;
		if (propagate(getTrailLiteralAt(i)))
			return true;
	}

	return false;
}

bool Propagator::propagateAll(void)
{
	int tempIndex = propagationStartIndex;
	propagationStartIndex = SolverInstance->trail.size();
#ifdef DEEP_PROPAGATOR_DEBUG
	if (debuggingEnabled)
		printf("propagator (%s): propagating from trail pos %d until trail pos %d\n", propagatorName, tempIndex, SolverInstance->trail.size());
#endif
	return propagate(tempIndex, SolverInstance->trail.size());
}

void Propagator::backjump(int level)
{
	cancelUntil(level);
	if (propagationStartIndex > SolverInstance->trail_lim[level])
		propagationStartIndex = SolverInstance->trail_lim[level];
}

