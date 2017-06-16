/* -*- Mode: C; indent-tabs-mode: t; c-basic-offset: 2; tab-width: 2 -*-  */
/*
 * TriggerProtectedPropagator.h
 * Copyright (C) 2015 Shahab Tasharrofi <>
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

#ifndef _TRIGGER_PROTECTED_PROPAGATOR_H_
#define _TRIGGER_PROTECTED_PROPAGATOR_H_

#include "Propagator.h"

class TriggerProtectedPropagator: public Propagator 
{
	public:
		TriggerProtectedPropagator(Solver *S) : Propagator(S) { }

		virtual bool triggersReady() = 0;								// Returns true if triggers are computed and ready to use.
		virtual const vec<Lit> &getTriggers(void) = 0;	// Returns a clause that, if not satisfied (different from being
																										//   falsified in three valued semantics), then the propagator
																										//   cannot detect any new inconsistency;
																										// Should only be called after "triggersReady" method returns true
																										// If set S of literals are returned, it means that the propagator
																										//   is satisfied as long as none of the literals in S are assigned
																										//   true (i.e., as long as clause V{S} is not satisfied).
};

#endif // _TRIGGER_PROTECTED_PROPAGATOR_H_

