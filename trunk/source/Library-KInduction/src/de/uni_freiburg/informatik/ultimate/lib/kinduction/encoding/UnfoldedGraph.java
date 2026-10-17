/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * The abstraction seen through {@link CallNode}s: every node keeps the chain of call sites it was reached through,
 * and an internal transition keeps that chain, because it stays inside one procedure activation.
 * <p>
 * Calls and returns are <b>not</b> transitions of this graph. {@link ProcedureSummaries} resolves each of them
 * beforehand, either into a summary edge over the whole call-to-return span (a callee without loops) or into a pair
 * of virtual edges around an unfolded copy of the callee (a callee with loops). Both are virtual edges of
 * {@link LoopTreeFormulaBuilder}, so reporting no call and no return transition here is not a way of ignoring them
 * - it states that none is left.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type of the abstraction
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class UnfoldedGraph<LETTER extends IAction, STATE>
		implements ICallResolvedGraph<LETTER, CallNode<STATE>> {

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;

	public UnfoldedGraph(final INestedWordAutomaton<LETTER, STATE> abstraction) {
		mAbstraction = abstraction;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, CallNode<STATE>>> internalSuccessors(
			final CallNode<STATE> node) {
		final List<OutgoingInternalTransition<LETTER, CallNode<STATE>>> result = new ArrayList<>();
		for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(node.getState())) {
			result.add(new OutgoingInternalTransition<>(t.getLetter(), node.sibling(t.getSucc())));
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, CallNode<STATE>>> callSuccessors(final CallNode<STATE> node) {
		return Collections.emptyList();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, CallNode<STATE>>> returnSuccessorsGivenHier(
			final CallNode<STATE> node, final CallNode<STATE> hier) {
		return Collections.emptyList();
	}
}
