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

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * {@link IAbstractPostOperator} describes a post or pre operator for an {@link IAbstractDomain}. It is used to compute
 * the abstract post or pre state given an old {@link IAbstractState} and a transition.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public interface IAbstractPostOperator<STATE extends IAbstractState<STATE>, ACTION>
		extends IAbstractTransformer<STATE, ACTION> {

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

	/**
	 * Evaluate the given boolean formula under the given state.
	 *
	 * @param state
	 *            The state under the formula should be evaluated.
	 * @param formula
	 *            The boolean {@link Term} that should be evaluated.
	 * @param script
	 *            A {@link Script} that can be used during evaluation.
	 * @return {@link EvalResult#TRUE} if this state does not allow any valuation that makes the term equivalent to
	 *         false, {@link EvalResult#FALSE} if this state does not allow any valuation that makes the term equivalent
	 *         to true, and {@link EvalResult#UNKNOWN} otherwise. Note that in particular, an implementation that only
	 *         returns {@link EvalResult#UNKNOWN} is sound.
	 */
	EvalResult evaluate(STATE state, Term formula, Script script);

	/**
	 * The result of {@link IAbstractPostOperator#evaluate(Script, Term)}.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum EvalResult {
		TRUE,

		FALSE,

		UNKNOWN;

		/**
		 * Select one of the enum constants base on boolean conditions.
		 *
		 * @param selectTrue
		 *            Select TRUE
		 * @param selectFalse
		 *            Select FALSE
		 * @return {@link #TRUE}/{@link #FALSE} if only one of the corresponding flags was set, {@link #UNKNOWN} if no
		 *         flag was set.
		 * @throws IllegalArgumentException
		 *             both flags were set at the same time.
		 */
		public static EvalResult selectTF(final boolean selectTrue, final boolean selectFalse) {
			if (selectTrue && selectFalse) {
				throw new IllegalArgumentException("Selected TRUE and FALSE at the same time.");
			} else if (selectTrue) {
				return TRUE;
			} else if (selectFalse) {
				return FALSE;
			}
			return UNKNOWN;
		}
	}
}
