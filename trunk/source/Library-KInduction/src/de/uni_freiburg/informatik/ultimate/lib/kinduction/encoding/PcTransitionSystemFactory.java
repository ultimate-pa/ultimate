/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.LoopTreeFormulaBuilder.LoopTree;

/**
 * Builds the {@link PcTransitionSystem} of a nested word automaton, so that {@link KInduction} and everyone else who
 * reasons about the same program (e.g. an inductiveness check of invariant candidates) work on the identical encoding.
 * <p>
 * Building the loop tree composes transition formulas, which declares constants for their aux vars and thus locks the
 * script itself. So this must not be called while the caller holds the script's lock.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class PcTransitionSystemFactory {

	/**
	 * @param system
	 *            the transition system, over {@link CallNode}s of the automaton's states
	 * @param summaries
	 *            the resolved call sites, {@code null} if the automaton has no call transition
	 */
	public record Result<LETTER extends IAction, STATE>(PcTransitionSystem<CallNode<STATE>> system,
			ProcedureSummaries<LETTER, STATE> summaries) {
	}

	private PcTransitionSystemFactory() {
		// static only
	}

	/**
	 * The loop tree of the program, made a transition system. Its nodes are {@link CallNode}s: a state together with
	 * the call sites it was reached through. If the abstraction has no call transition every node is at depth zero and
	 * the tree is the whole automaton. Otherwise every call site is first resolved by {@link ProcedureSummaries} - into
	 * a virtual call edge if the callee can be summarized, into an unfolded copy of the callee if it contains a loop -
	 * and the tree is built for the resulting graph, which has no call and no return transition left. A call that
	 * stayed in it would be unsound, see {@link LoopTreeFormulaBuilder}.
	 */
	public static <LETTER extends IAction, STATE> Result<LETTER, STATE> build(final IUltimateServiceProvider services,
			final ILogger logger, final CfgSmtToolkit csToolkit, final ManagedScript mgdScript,
			final INestedWordAutomaton<LETTER, STATE> abstraction) {
		final LoopTree<CallNode<STATE>> tree;
		final ProcedureSummaries<LETTER, STATE> summaries;
		if (!hasCallTransitions(abstraction)) {
			summaries = null;
			tree = new LoopTreeFormulaBuilder<>(services, logger, mgdScript, new UnfoldedGraph<>(abstraction),
					roots(abstraction.getStates()), roots(abstraction.getInitialStates()),
					roots(abstraction.getFinalStates()), Collections.emptyMap(), Collections.emptySet()).build();
		} else {
			summaries = new ProcedureSummaries<>(services, logger, csToolkit, mgdScript, abstraction);
			tree = new LoopTreeFormulaBuilder<>(services, logger, mgdScript, summaries.getGraph(),
					summaries.getScopeStates(), summaries.getInitStates(), summaries.getFinalStates(),
					summaries.getVirtualCallEdges(), summaries.getSealedStates()).build();
		}
		return new Result<>(new PcTransitionSystem<>(tree), summaries);
	}

	/** The given states as nodes with no pending call, for a program in which nothing is ever called. */
	private static <STATE> Set<CallNode<STATE>> roots(final Iterable<STATE> states) {
		final Set<CallNode<STATE>> result = new LinkedHashSet<>();
		for (final STATE state : states) {
			result.add(CallNode.root(state));
		}
		return result;
	}

	private static <LETTER, STATE> boolean hasCallTransitions(final INestedWordAutomaton<LETTER, STATE> abstraction) {
		for (final STATE state : abstraction.getStates()) {
			if (abstraction.callSuccessors(state).iterator().hasNext()) {
				return true;
			}
		}
		return false;
	}
}
