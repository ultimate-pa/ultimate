/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 *
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Removes states which only have one outgoing transition and bends over all incoming transitions to the respective
 * target state.
 * <p>
 * In contrast to {@link SingleExitShrinker}, this shrinker replaces all such transitions with the same symbol in the
 * automaton in one go. This can sometimes be necessary.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see SingleExitShrinker
 */
public class CommonSingleExitShrinker<LETTER, STATE> extends AbstractShrinker<Set<Pair<STATE, STATE>>, LETTER, STATE> {
	/**
	 * @param services
	 *            Ultimate services.
	 */
	public CommonSingleExitShrinker(final IUltimateServiceProvider services) {
		super(services);
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> createAutomaton(final List<Set<Pair<STATE, STATE>>> list) {
		// create fresh automaton
		final INestedWordAutomaton<LETTER, STATE> automaton = mFactory.create(mAutomaton);

		// data structures to contain all transitive chains (forward & backward)
		final Map<STATE, STATE> left2right = new HashMap<>();

		final Set<STATE> states = new HashSet<>(mAutomaton.getStates());
		/*
		 * add states that are not a left-hand side in the list; also set up data structures containing all transitive
		 * chains
		 */
		for (final Set<Pair<STATE, STATE>> pairs : list) {
			SingleExitShrinker.fillTransitivityMaps(left2right, states, pairs);
		}

		SingleExitShrinker.constructResuLt(automaton, left2right, states, mAutomaton, mFactory);

		return automaton;
	}

	@Override
	public List<Set<Pair<STATE, STATE>>> extractList() {
		final Map<LETTER, Set<STATE>> internalLetter2statesWithSingleTransition = new HashMap<>();
		for (final STATE state : mAutomaton.getStates()) {
			final Iterator<LETTER> iterator = mAutomaton.lettersInternal(state).iterator();
			if (!iterator.hasNext()) {
				continue;
			}
			final LETTER letter = iterator.next();
			if (iterator.hasNext()) {
				continue;
			}
			addToMapIfDeterministic(letter, state, internalLetter2statesWithSingleTransition,
					mAutomaton::internalSuccessors);
		}

		final ArrayList<Set<Pair<STATE, STATE>>> list = new ArrayList<>();
		for (final Entry<LETTER, Set<STATE>> entry : internalLetter2statesWithSingleTransition.entrySet()) {
			final LETTER letter = entry.getKey();
			final Set<STATE> states = entry.getValue();
			final Set<Pair<STATE, STATE>> set = new HashSet<>(states.size());
			for (final STATE state : states) {
				set.add(new Pair<>(state, mAutomaton.internalSuccessors(state, letter).iterator().next().getSucc()));
			}
			list.add(set);
		}
		return list;
	}

	private void addToMapIfDeterministic(final LETTER letter, final STATE state, final Map<LETTER, Set<STATE>> map,
			final BiFunction<STATE, LETTER, Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>>> succProvider) {
		final Iterator<? extends IOutgoingTransitionlet<LETTER, STATE>> iterator =
				succProvider.apply(state, letter).iterator();
		iterator.next();
		if (iterator.hasNext()) {
			// nondeterministic
			return;
		}

		Set<STATE> set = map.get(letter);
		if (set == null) {
			set = new HashSet<>();
			map.put(letter, set);
		}
		set.add(state);
	}
}
