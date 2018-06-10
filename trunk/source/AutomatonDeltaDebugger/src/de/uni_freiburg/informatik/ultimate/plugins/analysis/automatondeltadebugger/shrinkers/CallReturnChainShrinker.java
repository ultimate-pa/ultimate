/*
 * Copyright (C) 2018 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils.LetterType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils.TypedLetter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils.TypedTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Removes transition chains from a call to the respective return transitions.
 * <p>
 * Example: A simple chain of four states connected by transitions "q1 -c-> q2 -a-> q3 -r/q1-> q4" can be simplified by
 * removing the call and return transitions and adding the transition "q1 -x-> q4", where "x" is some fresh symbol. For
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class CallReturnChainShrinker<LETTER, STATE> extends
		AbstractShrinker<Pair<List<TypedTransition<LETTER, STATE>>, List<TypedTransition<LETTER, STATE>>>, LETTER, STATE> {
	private static final String DEFAULT_DUMMY_INTERNAL_LETTER = "a";

	/**
	 * @param services
	 *            Ultimate services.
	 */
	public CallReturnChainShrinker(final IUltimateServiceProvider services) {
		super(services);
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> createAutomaton(
			final List<Pair<List<TypedTransition<LETTER, STATE>>, List<TypedTransition<LETTER, STATE>>>> list) {
		// create internal alphabet
		final Set<LETTER> internalAlphabet = new HashSet<>(mAutomaton.getVpAlphabet().getInternalAlphabet());
		final TypedLetter<LETTER> dummyLetter = getDummyLetter(internalAlphabet);
		internalAlphabet.add(dummyLetter.getLetter());

		// create fresh automaton
		final INestedWordAutomaton<LETTER, STATE> automaton = mFactory.create(internalAlphabet, null, null);

		// add all states
		mFactory.addStates(automaton, mAutomaton.getStates());

		// add the complement of the passed call and return transitions and add old and new internal transitions
		final Set<TypedTransition<LETTER, STATE>> internalTransitions = mFactory.getInternalTransitions(mAutomaton);
		final Set<TypedTransition<LETTER, STATE>> callTransitions = mFactory.getCallTransitions(mAutomaton);
		final Set<TypedTransition<LETTER, STATE>> returnTransitions = mFactory.getReturnTransitions(mAutomaton);
		for (final Pair<List<TypedTransition<LETTER, STATE>>, List<TypedTransition<LETTER, STATE>>> pair : list) {
			final List<TypedTransition<LETTER, STATE>> calls = pair.getFirst();
			callTransitions.removeAll(calls);
			final STATE pred = calls.iterator().next().getPred();
			final List<TypedTransition<LETTER, STATE>> returns = pair.getSecond();
			for (final TypedTransition<LETTER, STATE> returnTrans : returns) {
				internalTransitions.add(new TypedTransition<>(pred, returnTrans.getSucc(), null, dummyLetter));
				returnTransitions.remove(returnTrans);
			}
		}
		mFactory.addInternalTransitions(automaton, internalTransitions);
		mFactory.addCallTransitions(automaton, callTransitions);
		mFactory.addReturnTransitions(automaton, returnTransitions);

		return automaton;
	}

	@SuppressWarnings("unchecked")
	private TypedLetter<LETTER> getDummyLetter(final Set<LETTER> internalAlphabet) throws IllegalArgumentException {
		if (!internalAlphabet.isEmpty()) {
			// take the first existing internal letter
			return new TypedLetter<>(internalAlphabet.iterator().next(), LetterType.INTERNAL);
		}
		// create a new internal letter from a string (cast)
		return (TypedLetter<LETTER>) new TypedLetter<>(DEFAULT_DUMMY_INTERNAL_LETTER, LetterType.INTERNAL);
	}

	@Override
	public List<Pair<List<TypedTransition<LETTER, STATE>>, List<TypedTransition<LETTER, STATE>>>> extractList() {
		// collect call transitions by predecessor
		final Map<STATE, Set<TypedTransition<LETTER, STATE>>> pred2callTrans = new HashMap<>();
		for (final TypedTransition<LETTER, STATE> trans : mFactory.getCallTransitions(mAutomaton)) {
			Set<TypedTransition<LETTER, STATE>> set = pred2callTrans.get(trans.getPred());
			if (set == null) {
				set = new HashSet<>();
				pred2callTrans.put(trans.getPred(), set);
			}
			set.add(trans);
		}
		// collect return transitions by hierarchical predecessor
		final Map<STATE, Set<TypedTransition<LETTER, STATE>>> hierPred2RetTrans = new HashMap<>();
		for (final TypedTransition<LETTER, STATE> trans : mFactory.getReturnTransitions(mAutomaton)) {
			Set<TypedTransition<LETTER, STATE>> set = hierPred2RetTrans.get(trans.getHier());
			if (set == null) {
				set = new HashSet<>();
				hierPred2RetTrans.put(trans.getHier(), set);
			}
			set.add(trans);
		}
		// connect common call and return transitions
		final List<Pair<List<TypedTransition<LETTER, STATE>>, List<TypedTransition<LETTER, STATE>>>> result =
				new ArrayList<>(hierPred2RetTrans.size());
		for (final Entry<STATE, Set<TypedTransition<LETTER, STATE>>> entry : pred2callTrans.entrySet()) {
			final Set<TypedTransition<LETTER, STATE>> returns = hierPred2RetTrans.get(entry.getKey());
			if (returns != null) {
				result.add(new Pair<>(new ArrayList<>(entry.getValue()), new ArrayList<>(returns)));
			}
		}
		return result;
	}
}
