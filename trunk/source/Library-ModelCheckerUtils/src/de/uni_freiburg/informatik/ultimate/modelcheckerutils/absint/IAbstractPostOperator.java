/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint;

import java.util.List;

/**
 * {@link IAbstractPostOperator} describes a post or pre operator for an {@link IAbstractDomain}. It is used to compute
 * the abstract post or pre state given an old {@link IAbstractState} and a transition.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public interface IAbstractPostOperator<STATE extends IAbstractState<STATE, VARDECL>, ACTION, VARDECL>
		extends IAbstractTransformer<STATE, ACTION, VARDECL> {

	/**
	 * Compute the abstract post from two abstract STATEs and one ACTION. This is used for scope switching.
	 *
	 * @param stateBeforeLeaving
	 *            The abstract state in the old scope, i.e., the scope that we are leaving.
	 * @param secondState
	 *            Either the hierachical prestate or the state after leaving, depending on
	 *            {@link IAbstractDomain#useHierachicalPre()}.
	 *
	 *            A state after leaving is the abstract state in the new scope, i.e., the scope that we are entering.
	 *            This state has already all non-scope related variables set (
	 *            {@link IAbstractState#patch(IAbstractState)} was already applied).
	 * @param transition
	 *            The transition that caused the scope change.
	 * @return A new STATE that has the same variables as the old abstract state in the new scope and incorporates the
	 *         effects of the taken transition.
	 */
	List<STATE> apply(STATE stateBeforeLeaving, STATE secondState, ACTION transition);
}
