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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/**
 * Determinize a given tree automaton.
 * 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER>
 *            letter of the tree automaton.
 * @param <STATE>
 *            state of the tree automaton.
 */
public class Determinize<LETTER extends IRankedLetter, STATE> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final IMergeStateFactory<STATE> mStateFactoryMerge;
	private final ISinkStateFactory<STATE> mStateFactoryEmptyStack;
	private final Map<Set<STATE>, STATE> mReducedStates;

	protected final ITreeAutomatonBU<LETTER, STATE> mResult;
	private final AutomataLibraryServices mServices;

	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE>> Determinize(
			final AutomataLibraryServices services, final SF factory,
			final ITreeAutomatonBU<LETTER, STATE> tree) {
		mServices = services;
		mReducedStates = new HashMap<>();
		mStateFactoryMerge = factory;
		mStateFactoryEmptyStack = factory;
		mTreeAutomaton = tree;

		mResult = computeResult();
	}

	private STATE reduceState(final Set<STATE> key) {
		if (!mReducedStates.containsKey(key)) {
			mReducedStates.put(key, mStateFactoryMerge.merge(key));
		}
		return mReducedStates.get(key);
	}

	@Override
	public String startMessage() {
		return "Starting determinization";
	}

	@Override
	public String exitMessage() {
		return "Exiting determinization";
	}
	
	private TreeAutomatonBU<LETTER, STATE> constructFromRules(final Map<LETTER, Map<List<Set<STATE>>, Set<STATE>>> rules) {
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();
		res.extendAlphabet(mTreeAutomaton.getAlphabet());

		for (final LETTER letter : rules.keySet()) {
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(letter);
			for (final List<Set<STATE>> sSrc : mp.keySet()) {
				final List<STATE> src = new ArrayList<>();
				for (final Set<STATE> sub : sSrc) {
					src.add(reduceState(sub));
				}
				final Set<STATE> sDest = mp.get(sSrc);
				final STATE dest = reduceState(sDest);
				res.addRule(new TreeAutomatonRule<>(letter, src, dest));

				for (final Set<STATE> sub : sSrc) {
					final STATE state = reduceState(sub);
					for (final STATE s : sub) {
						if (mTreeAutomaton.isFinalState(s)) {
							res.addFinalState(state);
						}
					}
					
				}
				for (final STATE s : sDest) {
					if (mTreeAutomaton.isFinalState(s)) {
						res.addFinalState(dest);
					}
				}
			}
		}
		return res;
	}
	
	private ITreeAutomatonBU<LETTER, STATE> computeResult() {
		final Map<STATE, Set<STATE>> stateToSState = new HashMap<>();

		final Map<LETTER, Map<List<Set<STATE>>, Set<STATE>>> rules = new HashMap<>();

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
		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRules()) {
			if (!rules.containsKey(rule.getLetter())) {
				rules.put(rule.getLetter(), new HashMap<>());
			}
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(rule.getLetter());
			final List<Set<STATE>> source = new ArrayList<>();
			for (final STATE sr : rule.getSource()) {
				if (!stateToSState.containsKey(sr)) {
					final Set<STATE> nw = new HashSet<>();
					nw.add(sr);
					stateToSState.put(sr, nw);
				}
				source.add(stateToSState.get(sr));
			}
			final STATE sr = rule.getDest();
			if (!stateToSState.containsKey(sr)) {
				final Set<STATE> nw = new HashSet<>();
				nw.add(sr);
				stateToSState.put(sr, nw);
			}
			if (!mp.containsKey(source)) {
				mp.put(source, new HashSet<STATE>());
			}
			mp.get(source).add(sr);
		}

		final LinkedList<Set<STATE>> worklist = new LinkedList<>();
		for (final Entry<LETTER, Map<List<Set<STATE>>, Set<STATE>>> letterRule : rules.entrySet()) {
			final Map<List<Set<STATE>>, Set<STATE>> mp = letterRule.getValue();
			for (final Entry<List<Set<STATE>>, Set<STATE>> st : mp.entrySet()) {
				if (st.getValue().size() > 1) {
					worklist.add(st.getValue());
				}
			}
		}
		final Set<Set<STATE>> visited = new HashSet<>();
		while (!worklist.isEmpty()) {
			final Set<STATE> state = worklist.poll();
			if (visited.contains(state)) {
				continue;
			}
			visited.add(state);
			final Map<LETTER, Map<List<Set<STATE>>, Set<Set<STATE>>>> newRules = new HashMap<>();
			for (final Entry<LETTER, Map<List<Set<STATE>>, Set<STATE>>> letterRule : rules.entrySet()) {
				final LETTER letter = letterRule.getKey();
				if (!newRules.containsKey(letter)) {
					newRules.put(letter, new HashMap<>());
				}
				final Map<List<Set<STATE>>, Set<STATE>> mp = letterRule.getValue();
				for (final Entry<List<Set<STATE>>, Set<STATE>> srcDest : mp.entrySet()) {
					final ArrayList<Set<STATE>> src = (ArrayList<Set<STATE>>) srcDest.getKey();
					final Set<STATE> dest = srcDest.getValue();
					// letter(src) -> dest
					int idx = 0;
					for (final Set<STATE> srcQ : src) {
						if (state.containsAll(srcQ)) {
							@SuppressWarnings("unchecked")
							final ArrayList<Set<STATE>> toAdd = (ArrayList<Set<STATE>>) src.clone();
							toAdd.set(idx, state);

							if (!newRules.get(letter).containsKey(toAdd)) {
								newRules.get(letter).put(toAdd, new HashSet<Set<STATE>>());
							}
							newRules.get(letter).get(toAdd).add(dest);
						}
						++idx;
					}
				}
			}
			for (final LETTER letter : newRules.keySet()) {
				final Map<List<Set<STATE>>, Set<Set<STATE>>> mp = newRules.get(letter);
				for (final List<Set<STATE>> st : mp.keySet()) {

					final Set<Set<STATE>> dest = mp.get(st);
					final Set<STATE> uni = new HashSet<>();
					for (final Set<STATE> s : dest) {
						uni.addAll(s);
					}
					rules.get(letter).put(st, uni);
					if (mp.get(st).size() > 1) {
						worklist.add(uni);
					}
				}
			}
		}

		final TreeAutomatonBU<LETTER, STATE> det = constructFromRules(rules);
		final Totalize<LETTER, STATE> op = new Totalize<>(mServices, mStateFactoryEmptyStack, det);
		return op.getResult();
	}

	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
