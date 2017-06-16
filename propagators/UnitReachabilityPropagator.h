/* -*- Mode: C; indent-tabs-mode: t; c-basic-offset: 2; tab-width: 2 -*-  */
/*
 * UnitReachabilityPropagator.h
 * Copyright (C) 2015 Shahab Tasharrofi <shahab.tasharrofi@gmail.com>
 *
 * graphsat is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * graphsat is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef _UNIT_REACHABILITY_PROPAGATOR_H_
#define _UNIT_REACHABILITY_PROPAGATOR_H_

#include <unordered_map>
#include <vector>

#include "utils/FixedSizeIntMap.h"
#include "utils/GraphUtils.h"
#include "Propagator.h"

using namespace std;

class UnitReachabilityPropagator: public Propagator 
{
private:
	vec<Lit> urnrClause;

	SATGraph *graph;
	SATGraph reachGraph;
	FixedSizeIntMap< pair<int, int> > reachabilityPairsByLiteral;
	FixedSizeIntMap< pair<int, int> > nonReachabilityPairsByLiteral;
	vector< vector< pair<int, Lit> > > reachabilities; // reachabilities[i][j] = (k, p) means that v_k should be reachable from v_i whenever p is true
	vector< vector< pair<int, Lit> > > nonReachabilities; // nonReachabilities[i][j] = (k, p) means that v_k should not be reachable from v_i whenever p is true

	OrderedDFSTree forwardReachableNodes;
	OrderedDFSTree backwardReachableNodes;

	void pushNegatedPathToRoot(const OrderedDFSTree &tree, int node);
	bool propagateReachability(int source, int dest, Lit p);
	bool propagateNonReachability(int source, int dest, Lit p);
public:
	UnitReachabilityPropagator(Solver *solver, SATGraph *graph, const unordered_map<int, unordered_map<int, Lit> > &reachabilities, const unordered_map<int, unordered_map<int, Lit> > &nonReachabilities);

	virtual bool initialize(void) override;
	virtual bool propagate(Lit p) override;
	virtual const vec<Lit> &explain() override;
	virtual bool isTheoryVar(Var v) override;

	virtual Propagator *copy(Solver *S) override;
};

#endif // _UNIT_REACHABILITY_PROPAGATOR_H_

