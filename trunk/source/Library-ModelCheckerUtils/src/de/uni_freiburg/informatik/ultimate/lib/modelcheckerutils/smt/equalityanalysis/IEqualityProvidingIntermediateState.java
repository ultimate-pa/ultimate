/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public interface IEqualityProvidingIntermediateState {

	/**
	 * Determine if the given two terms must be equal in this state.
	 *
	 * @param t1
	 * @param t2
	 * @return
	 */
	boolean areEqual(Term t1, Term t2);

	/**
	 * Determine if the given two terms must be unequal in this state.
	 *
	 * @param t1
	 * @param t2
	 * @return
	 */
	boolean areUnequal(Term t1, Term t2);

//	/**
//	 * Compute the join of two states, i.e., compute a state which only contains constraints that are implied by this
//	 *  and the given other state
//	 *
//	 * @param other
//	 * @return
//	 */
//	@Deprecated
//	IEqualityProvidingIntermediateState join(IEqualityProvidingIntermediateState other);

	boolean isBottom();

	Set<Term> getSetConstraintForExpression(Term locArraySelect);
}
