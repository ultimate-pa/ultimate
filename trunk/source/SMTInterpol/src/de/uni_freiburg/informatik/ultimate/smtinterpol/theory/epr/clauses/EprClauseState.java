/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

/**
 * The states that an EprClause can have, it can be
 *  - fulfilled: at least one literal is fulfilled (on all points)
 *  - "normal": no literal is fulfilled on all points, there is no point where the clause is unit or a conflict
 *  - unit: on at least one point all literals except one are refuted, that one is unconstrained
 *  - conflict: on at least one point all literals are refuted
 *
 * @author nutz
 */
public enum EprClauseState {
	Fulfilled, Normal, Unit, Conflict
}
