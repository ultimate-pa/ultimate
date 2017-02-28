/*
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2014-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/**
 * Determinize a given tree automaton.
 * 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <R>
 *            letter of the tree automaton.
 * @param <S>
 *            state of the tree automaton.
 */
public class Determinize<R, S> implements IOperation<R, S, IStateFactory<S>> {

	private final ITreeAutomatonBU<R, S> mTreeAutomaton;
	private final IMergeStateFactory<S> mStateFactoryMerge;
	private final IEmptyStackStateFactory<S> mStateFactoryEmptyStack;
	private final Map<Set<S>, S> mReducedStates;

	protected final ITreeAutomatonBU<R, S> mResult;
	private final AutomataLibraryServices mServices;

	public <F extends IMergeStateFactory<S> & IEmptyStackStateFactory<S>> Determinize(
			final AutomataLibraryServices services, final F factory,
			final ITreeAutomatonBU<R, S> tree) {
		mServices = services;
		mReducedStates = new HashMap<>();
		mStateFactoryMerge = factory;
		mStateFactoryEmptyStack = factory;
		mTreeAutomaton = tree;

		mResult = computeResult();
	}

	private S reduceState(final Set<S> key) {
		if (!mReducedStates.containsKey(key)) {
			mReducedStates.put(key, mStateFactoryMerge.merge(key));
		}
		return mReducedStates.get(key);
	}

	@Override
	public String operationName() {
		return "Determinization";
	}

	@Override
	public String startMessage() {
		return "Starting determinization";
	}

	@Override
	public String exitMessage() {
		return "Exiting determinization";
	}
	
	private TreeAutomatonBU<R, S> constructFromRules(final Map<R, Map<List<Set<S>>, Set<S>>> rules) {
		final TreeAutomatonBU<R, S> res = new TreeAutomatonBU<>();
		res.extendAlphabet(mTreeAutomaton.getAlphabet());

		for (final R letter : rules.keySet()) {
			final Map<List<Set<S>>, Set<S>> mp = rules.get(letter);
			for (final List<Set<S>> sSrc : mp.keySet()) {
				final List<S> src = new ArrayList<>();
				for (final Set<S> sub : sSrc) {
					src.add(reduceState(sub));
				}
				final Set<S> sDest = mp.get(sSrc);
				final S dest = reduceState(sDest);
				res.addRule(new TreeAutomatonRule<>(letter, src, dest));

				for (final Set<S> sub : sSrc) {
					final S state = reduceState(sub);
					for (final S s : sub) {
						if (mTreeAutomaton.isInitialState(s)) {
							res.addInitialState(state);
						}
						if (mTreeAutomaton.isFinalState(s)) {
							res.addFinalState(state);
						}
					}
					
				}
				for (final S s : sDest) {
					if (mTreeAutomaton.isFinalState(s)) {
						res.addFinalState(dest);
					}
					if (mTreeAutomaton.isInitialState(s)) {
						res.addInitialState(dest);
					}
				}
			}
		}
		return res;
	}
	
	private ITreeAutomatonBU<R, S> computeResult() {
		final Map<S, Set<S>> stateToSState = new HashMap<>();

		final Map<R, Map<List<Set<S>>, Set<S>>> rules = new HashMap<>();

		/*
		 * // Dummy rules final STATE dummyState = stateFactory.createEmptyStackState(); final Set<STATE> superSet = new
		 * HashSet<STATE>(); superSet.addAll(treeAutomaton.getStates()); superSet.add(dummyState);
		 * 
		 * if (!stateToSState.containsKey(dummyState)) { final Set<STATE> nw = new HashSet<>(); nw.add(dummyState);
		 * stateToSState.put(dummyState, nw); } for (final TreeAutomatonRule<LETTER, STATE> rule :
		 * treeAutomaton.getRules()) { if (!rules.containsKey(rule.getLetter())) { rules.put(rule.getLetter(), new
		 * HashMap<>()); } final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(rule.getLetter()); final
		 * List<Set<STATE>> source = new ArrayList<>(); for (int i = 0; i < rule.getSource().size(); ++i) {
		 * source.add(superSet); } if (!mp.containsKey(source)) { mp.put(source, new HashSet<STATE>()); }
		 * mp.get(source).add(dummyState); } // Dummy Rules end.
		 */
		for (final TreeAutomatonRule<R, S> rule : mTreeAutomaton.getRules()) {
			if (!rules.containsKey(rule.getLetter())) {
				rules.put(rule.getLetter(), new HashMap<>());
			}
			final Map<List<Set<S>>, Set<S>> mp = rules.get(rule.getLetter());
			final List<Set<S>> source = new ArrayList<>();
			for (final S sr : rule.getSource()) {
				if (!stateToSState.containsKey(sr)) {
					final Set<S> nw = new HashSet<>();
					nw.add(sr);
					stateToSState.put(sr, nw);
				}
				source.add(stateToSState.get(sr));
			}
			final S sr = rule.getDest();
			if (!stateToSState.containsKey(sr)) {
				final Set<S> nw = new HashSet<>();
				nw.add(sr);
				stateToSState.put(sr, nw);
			}
			if (!mp.containsKey(source)) {
				mp.put(source, new HashSet<S>());
			}
			mp.get(source).add(sr);
		}

		final LinkedList<Set<S>> worklist = new LinkedList<>();
		for (final Entry<R, Map<List<Set<S>>, Set<S>>> letterRule : rules.entrySet()) {
			final Map<List<Set<S>>, Set<S>> mp = letterRule.getValue();
			for (final Entry<List<Set<S>>, Set<S>> st : mp.entrySet()) {
				if (st.getValue().size() > 1) {
					worklist.add(st.getValue());
				}
			}
		}
		final Set<Set<S>> visited = new HashSet<>();
		while (!worklist.isEmpty()) {
			final Set<S> state = worklist.poll();
			if (visited.contains(state)) {
				continue;
			}
			visited.add(state);
			final Map<R, Map<List<Set<S>>, Set<Set<S>>>> newRules = new HashMap<>();
			for (final Entry<R, Map<List<Set<S>>, Set<S>>> letterRule : rules.entrySet()) {
				final R letter = letterRule.getKey();
				if (!newRules.containsKey(letter)) {
					newRules.put(letter, new HashMap<>());
				}
				final Map<List<Set<S>>, Set<S>> mp = letterRule.getValue();
				for (final Entry<List<Set<S>>, Set<S>> srcDest : mp.entrySet()) {
					final ArrayList<Set<S>> src = (ArrayList<Set<S>>) srcDest.getKey();
					final Set<S> dest = srcDest.getValue();
					// letter(src) -> dest
					int idx = 0;
					for (final Set<S> srcQ : src) {
						if (state.containsAll(srcQ)) {
							@SuppressWarnings("unchecked")
							final ArrayList<Set<S>> toAdd = (ArrayList<Set<S>>) src.clone();
							toAdd.set(idx, state);

							if (!newRules.get(letter).containsKey(toAdd)) {
								newRules.get(letter).put(toAdd, new HashSet<Set<S>>());
							}
							newRules.get(letter).get(toAdd).add(dest);
						}
						++idx;
					}
				}
			}
			for (final R letter : newRules.keySet()) {
				final Map<List<Set<S>>, Set<Set<S>>> mp = newRules.get(letter);
				for (final List<Set<S>> st : mp.keySet()) {

					final Set<Set<S>> dest = mp.get(st);
					final Set<S> uni = new HashSet<>();
					for (final Set<S> s : dest) {
						uni.addAll(s);
					}
					rules.get(letter).put(st, uni);
					if (mp.get(st).size() > 1) {
						worklist.add(uni);
					}
				}
			}
		}

		final Totalize<R, S> op = new Totalize<>(mServices, mStateFactoryEmptyStack, constructFromRules(rules));
		return op.getResult();
	}

	@Override
	public ITreeAutomatonBU<R, S> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<S> stateFactory) throws AutomataLibraryException {
		return false;
	}
}
