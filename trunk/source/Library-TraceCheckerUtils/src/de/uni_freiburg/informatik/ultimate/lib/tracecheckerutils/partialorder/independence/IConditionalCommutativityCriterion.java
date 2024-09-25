/*
 * Copyright (C) 2023 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Criterion for conditional commutativity checking.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public interface IConditionalCommutativityCriterion<L> {

	/**
	 * Decide whether we should check for the conditional commutativity of letter1 and letter2 under the given state.
	 * 
	 * @param state
	 *            State
	 * @param letter1
	 *            A letter, which should be from an outgoing transition of the given state
	 * @param letter2
	 *            Another letter, which should be from an outgoing transition of the given state
	 * @return true if we should check and false otherwise
	 */
	boolean decide(IPredicate state, L letter1, L letter2);

	/**
	 * Decide whether we should try to proof the given commutativity condition.
	 * 
	 * @param condition
	 *            A commutativity condition
	 * @return true if we should check and false otherwise
	 */
	boolean decide(IPredicate condition);

	/**
	 * Allows to update the abstraction. Most criteria do not need to do implement this method.
	 * 
	 * @param abstraction
	 *            The abstraction
	 */
	default void updateAbstraction(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
	}

	/**
	 * Allows to update the criterion using the given state and letters. Most criteria do not need to do implement this
	 * method.
	 * 
	 * @param state
	 *            State
	 * @param letter1
	 *            A letter
	 * @param letter2
	 *            Another letter
	 */
	default void updateCriterion(final IPredicate state, final L letter1, final L letter2) {
		// most criteria do not need to do anything here
	}
}
