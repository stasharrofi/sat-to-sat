/* -*- Mode: C; indent-tabs-mode: t; c-basic-offset: 2; tab-width: 2 -*-  */
/*
 * GeneralizedPropagator.h
 * Copyright (C) 2015 Shahab Tasharrofi <shahab@pc41>
 *
 * minisat-general-propagators is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * minisat-general-propagators is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef _GENERALIZED_PROPAGATOR_H_
#define _GENERALIZED_PROPAGATOR_H_

#include <unordered_set>
#include <unordered_map>

#include "utils/FixedSizeIntSet.h"
#include "utils/FixedSizeIntMap.h"
#include "TriggerProtectedPropagator.h"

using namespace std;

class GeneralizedPropagator: public TriggerProtectedPropagator
{
	private:
		bool triggersInitialized;
		bool hasCompleteEncoding;

		vec<Lit> reason;
		vec<Lit> assumptions;
		vec<Lit> explanationAssumptions;
		Solver *newSolverInstance;

		FixedSizeIntSet<EnumerabilityTrait> triggers;
		// triggers: set of literals that, if becoming true, trigger the propagator execution
		FixedSizeIntSet<EnumerabilityTrait> reasonLiterals;
		// reasonLiterals: set of literals that should be inserted into reason clause.
		// keeping them as a set prevents multiple insertion of them.

		/* In the following, upperboundMap and lowerboundMap are the variables whose value
		 * will be assumed when search procedure of newSolverInstance is called.
		 * 
		 * Informally, (v --> v') \in upperboundMap means that our assumed value for v' would
		 * be the upperbound of current value for v (which could be unknown).
		 * 
		 * Similarly, (v --> v') \in lowerboundMap means that our assumed value for v' would
		 * be the lowerbound of current value for v (which could be unknown).
		 */
		FixedSizeIntMap<Var> upperboundMap;
		// upperboundMap: mapping v --> v' sets v':=false if v==false and sets v':=true otherwise
		FixedSizeIntMap<Var> lowerboundMap;
		// lowerboundMap: mapping v --> v' sets v':=true if v==true and sets v':=false otherwise
		FixedSizeIntMap<Var> reverseMapping;
		// reverseMapping: maps variables in upperbound or lowerbound to their source in external solver, i.e.,
		// if v --> v' in lower or upper bound then v' --> v in reverseMapping
		// used to translate a reasons and triggers into the language of external solver

		FixedSizeIntMap<int> varToAssumptionIndex;
		// varToAssumptionIndex: v --> i means that variable v is currently stored at position i of assumption vector
		int currentAssumptionIndex;
		// currentAssumptionIndex: Shows the last assumption index that is currently filled. Every literal in the
		// assumption vector after the currentAssumptionIndex should denote unknown value. That is, if
		// currentAssumptionIndex is n and we have a variable v so that varToAssumptionIndex[v] = m >= n then the
		// two following conditions should hold:
		// (1) If v is the upperbound of some variable v' in the outer solver then assumptions[m] = v
		// (2) If v is the lowerbound of some variable v' in the outer solver then assumptions[m] = ~v

		vector< pair<Lit, vector<Lit> > > reasonGenerator;
		// reasonGenerator: here l --> (l_1, ..., l_n) means that literal l should be included in the reason if
		// all l_1 ... l_n are true

		/* prepareReasonsOrTriggers: does the following:
		 * (1) Calls internal solver using the current assumptions
		 * (2) Depending on the internal solver's result, does one of the following:
		 * (2.a) If the internal solver finds a solution, fills reasonLiterals and unnecessaryLiterals
		 * (2.b) If the internal solver does not find a solution and "computeTriggers" is set, fills triggers
		 * (3) Returns true if and only if case (2.b) happened
		 */
		bool prepareReasonAndTriggers(bool computeTriggers);
		/* performPropagations: Calls "prepareReasonsOrTriggers" and tries to minimize reasons or triggers.
		 * If conflict is found then reports it to then external solver.
		 */
		bool performPropagations();
		void addAssumption(Lit p)
		{
			Var externalVar = var(p);

			if (upperboundMap.hasKey(externalVar))
			{
				Var internalVar = upperboundMap.valueOf(externalVar);

				int tmpNewPosition = varToAssumptionIndex.valueOf(internalVar);
				if (tmpNewPosition >= currentAssumptionIndex)
				{
					assumptions[tmpNewPosition] = assumptions[currentAssumptionIndex];
					assumptions[currentAssumptionIndex] = mkLit(internalVar, sign(p));
					varToAssumptionIndex.insert(internalVar, currentAssumptionIndex);
					varToAssumptionIndex.insert(var(assumptions[tmpNewPosition]), tmpNewPosition);
					currentAssumptionIndex++;
				}
			}

			if (lowerboundMap.hasKey(externalVar))
			{
				Var internalVar = lowerboundMap.valueOf(externalVar);

				int tmpNewPosition = varToAssumptionIndex.valueOf(internalVar);
				if (tmpNewPosition >= currentAssumptionIndex)
				{
					assumptions[tmpNewPosition] = assumptions[currentAssumptionIndex];
					assumptions[currentAssumptionIndex] = mkLit(internalVar, sign(p));
					varToAssumptionIndex.insert(internalVar, currentAssumptionIndex);
					varToAssumptionIndex.insert(var(assumptions[tmpNewPosition]), tmpNewPosition);
					currentAssumptionIndex++;
				}
			}
		}

		void removeAssumption(Lit p)
		{
			Var externalVar = var(p);

			if (upperboundMap.hasKey(externalVar))
			{
				Var internalUpVar = upperboundMap.valueOf(externalVar);
				int internalVarPos = varToAssumptionIndex.valueOf(internalUpVar);
				if (internalVarPos < currentAssumptionIndex)
				{
					currentAssumptionIndex--;
					if (internalVarPos < currentAssumptionIndex)
					{
						assumptions[internalVarPos] = assumptions[currentAssumptionIndex];
						varToAssumptionIndex.insert(var(assumptions[currentAssumptionIndex]), internalVarPos);
						varToAssumptionIndex.insert(internalUpVar, currentAssumptionIndex);
						internalVarPos = currentAssumptionIndex;
					}
					assumptions[internalVarPos] = mkLit(internalUpVar);
				}
			}

			if (lowerboundMap.hasKey(externalVar))
			{
				Var internalLowVar = lowerboundMap.valueOf(externalVar);
				int internalVarPos = varToAssumptionIndex.valueOf(internalLowVar);
				if (internalVarPos < currentAssumptionIndex)
				{
					currentAssumptionIndex--;
					if (internalVarPos < currentAssumptionIndex)
					{
						assumptions[internalVarPos] = assumptions[currentAssumptionIndex];
						varToAssumptionIndex.insert(var(assumptions[currentAssumptionIndex]), internalVarPos);
						varToAssumptionIndex.insert(internalLowVar, currentAssumptionIndex);
						internalVarPos = currentAssumptionIndex;
					}
					assumptions[internalVarPos] = ~mkLit(internalLowVar);
				}
			}
		}

		void clearAllAssumptions()
		{
			while (currentAssumptionIndex > 0)
				removeAssumption(mkLit(reverseMapping.valueOf(var(assumptions[currentAssumptionIndex - 1]))));
		}
	protected:
		// Overridden protected methods from Propagator class
		virtual bool propagate(int start, int end) override;
		virtual bool propagate(Lit p) override;
		virtual void cancelUntil(int level) override;
	public:
		GeneralizedPropagator(Solver *S, Solver *internalSolver, bool completeEncoding,
		                      int externalSolverVarCount, int internalSolverVarCount,
		                      const vector< pair<Var, Var> > &upperboundMapping,
		                      const vector< pair<Var, Var> > &lowerboundMapping,
		                      const vector< pair<Lit, vector<Lit> > > &conditionalReasons);

		// Overridden public methods from Propagator class
		virtual bool initialize(void) override;
		virtual const vec<Lit> &explain() override;
		virtual bool isTheoryVar(Var v) override;

		// Overridden public methods from TriggerProtectedPropagator class
		virtual bool triggersReady(void) override;
		virtual const vec<Lit> &getTriggers(void) override;

		virtual Propagator *copy(Solver *S);
};

#endif // _GENERALIZED_PROPAGATOR_H_

