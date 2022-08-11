/*
 * Copyright (C) 2022 Dennis Wölfing
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.maximalcausality;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;

/**
 * A state in the representative automaton.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters.
 */
public interface IMcrState<L extends IIcfgTransition<?>> extends IMLPredicate {
	/**
	 * Gets the new automaton state after executing a given transition.
	 *
	 * @param transition
	 *            The transition to take.
	 * @param newState
	 *            The new state in the original automaton.
	 * @param ranks
	 *            A map from transitions to ranks.
	 * @return A new state for the representative automaton, or null if the transition should be omitted.
	 */
	IMcrState<L> getNextState(L transition, IMLPredicate newState, Map<L, Integer> ranks, boolean optimizeForkJoin,
			boolean overapproximateWrwc);

	/**
	 * Gets the corresponding state in the original automaton.
	 *
	 * @return A state from the original automaton.
	 */
	IMLPredicate getOldState();

	/**
	 * Checks whether traces ending in the current state are representatives.
	 *
	 * @return true if every trace ending in the current state is a representative.
	 */
	boolean isRepresentative();
}
