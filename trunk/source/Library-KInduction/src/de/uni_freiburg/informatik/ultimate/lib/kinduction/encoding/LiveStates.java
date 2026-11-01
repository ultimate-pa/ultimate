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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * The states of a nested word automaton that can still matter for reachability: those from which an error
 * (accepting) state is reachable, those from which their procedure can return, and the initial states.
 * <p>
 * Every other state is a dead end. No path to an error runs through it, and none through a call that returns,
 * so leaving it out of the encoding changes no verdict. What it saves is structure: an infinite loop that only
 * cuts off a path - {@code ldv_stop}, the {@code while(1);} of {@code ldv_assume} or {@code abort} - is a loop of
 * the procedure, so the procedure had no loop-free summary and was unfolded at every call site, and so was every
 * procedure that calls it. Without its dead states such a procedure is loop-free, or has no state at all if it
 * never returns, and a call to it is a dead end as well.
 * <p>
 * The analysis is interprocedural and over-approximates both properties, which keeps more states than necessary
 * but never too few:
 * <ul>
 * <li><b>returns</b>: a state with a return transition; an internal predecessor of one that returns; a call site
 * whose callee returns from its entry state and that has a return successor that returns.
 * <li><b>reaches an error</b>: an accepting state; an internal predecessor of one that reaches an error; a call site
 * whose callee reaches an error from its entry state; a call site whose callee returns and that has a return
 * successor that reaches an error.
 * </ul>
 * Whether a callee that returns from its entry state returns through the very exit a return transition leaves from
 * is not checked, so a call site may be kept although that one return is impossible.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class LiveStates {

	private LiveStates() {
		// static only
	}

	/** @return the live states of {@code abstraction}, see the class javadoc */
	public static <LETTER extends IAction, STATE> Set<STATE> compute(
			final INestedWordAutomaton<LETTER, STATE> abstraction) {
		final Map<STATE, List<STATE>> callSitesByEntry = new HashMap<>();
		final Map<STATE, List<STATE>> entriesByCallSite = new HashMap<>();
		final Map<STATE, List<STATE>> callSitesByReturnSite = new HashMap<>();
		final Map<STATE, List<STATE>> returnSitesByCallSite = new HashMap<>();
		final Set<STATE> exits = new LinkedHashSet<>();
		for (final STATE state : abstraction.getStates()) {
			for (final OutgoingCallTransition<LETTER, STATE> call : abstraction.callSuccessors(state)) {
				callSitesByEntry.computeIfAbsent(call.getSucc(), k -> new ArrayList<>()).add(state);
				entriesByCallSite.computeIfAbsent(state, k -> new ArrayList<>()).add(call.getSucc());
			}
			for (final OutgoingReturnTransition<LETTER, STATE> ret : abstraction.returnSuccessors(state)) {
				exits.add(state);
				callSitesByReturnSite.computeIfAbsent(ret.getSucc(), k -> new ArrayList<>()).add(ret.getHierPred());
				returnSitesByCallSite.computeIfAbsent(ret.getHierPred(), k -> new ArrayList<>()).add(ret.getSucc());
			}
		}

		// returns
		final Set<STATE> returns = new LinkedHashSet<>();
		final Deque<STATE> worklist = new ArrayDeque<>();
		for (final STATE exit : exits) {
			add(returns, worklist, exit);
		}
		while (!worklist.isEmpty()) {
			final STATE state = worklist.poll();
			for (final IncomingInternalTransition<LETTER, STATE> t : abstraction.internalPredecessors(state)) {
				add(returns, worklist, t.getPred());
			}
			// state as a return site: its call site returns if the callee does
			for (final STATE callSite : get(callSitesByReturnSite, state)) {
				if (anyIn(get(entriesByCallSite, callSite), returns)) {
					add(returns, worklist, callSite);
				}
			}
			// state as a callee's entry: its call sites return if one of their return sites does
			for (final STATE callSite : get(callSitesByEntry, state)) {
				if (anyIn(get(returnSitesByCallSite, callSite), returns)) {
					add(returns, worklist, callSite);
				}
			}
		}

		// reaches an error
		final Set<STATE> error = new LinkedHashSet<>();
		for (final STATE accepting : abstraction.getFinalStates()) {
			add(error, worklist, accepting);
		}
		while (!worklist.isEmpty()) {
			final STATE state = worklist.poll();
			for (final IncomingInternalTransition<LETTER, STATE> t : abstraction.internalPredecessors(state)) {
				add(error, worklist, t.getPred());
			}
			// state as a callee's entry: the error is reached inside the callee
			for (final STATE callSite : get(callSitesByEntry, state)) {
				add(error, worklist, callSite);
			}
			// state as a return site: reached after the call returns
			for (final STATE callSite : get(callSitesByReturnSite, state)) {
				if (anyIn(get(entriesByCallSite, callSite), returns)) {
					add(error, worklist, callSite);
				}
			}
		}

		final Set<STATE> result = new LinkedHashSet<>();
		for (final STATE initial : abstraction.getInitialStates()) {
			result.add(initial);
		}
		result.addAll(returns);
		result.addAll(error);
		return result;
	}

	private static <STATE> void add(final Set<STATE> set, final Deque<STATE> worklist, final STATE state) {
		if (set.add(state)) {
			worklist.add(state);
		}
	}

	private static <STATE> List<STATE> get(final Map<STATE, List<STATE>> map, final STATE key) {
		return map.getOrDefault(key, Collections.emptyList());
	}

	private static <STATE> boolean anyIn(final List<STATE> states, final Set<STATE> set) {
		for (final STATE state : states) {
			if (set.contains(state)) {
				return true;
			}
		}
		return false;
	}
}
