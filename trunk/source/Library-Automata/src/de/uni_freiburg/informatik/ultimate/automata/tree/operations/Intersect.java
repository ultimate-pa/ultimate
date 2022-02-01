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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Intersect 2 tree automatons.
 *
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER>
 *            letter of the tree automatons.
 * @param <STATE>
 *            state of the tree automatons.
 */
public class Intersect<LETTER extends IRankedLetter, STATE>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>>
		implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeA;
	private final ITreeAutomatonBU<LETTER, STATE> mTreeB;
	protected final ITreeAutomatonBU<LETTER, STATE> mResult;

	private final IIntersectionStateFactory<STATE> mStateFactory;
	private final Map<STATE, Map<STATE, Pair<STATE, STATE>>> mPairsMap;
	private final Map<Pair<STATE, STATE>, STATE> mReducedStates;

	/**
	 *
	 * NOTE: because of a convention in TestFileInterpreter, if an argument for
	 * the operation is a StateFactory, it must be the first argument same for
	 * Services, both: first services then StateFactory
	 *
	 * @param services
	 * @param factory
	 * @param t1
	 * @param t2
	 */
	public Intersect(final AutomataLibraryServices services, final IIntersectionStateFactory<STATE> factory,
			final ITreeAutomatonBU<LETTER, STATE> t1, final ITreeAutomatonBU<LETTER, STATE> t2) {
		super(services);
		mReducedStates = new HashMap<>();
		mPairsMap = new HashMap<>();

		mStateFactory = factory;
		mTreeA = t1;
		mTreeB = t2;
		mResult = computeResult();
	}

	private STATE reduceState(final Pair<STATE, STATE> key) {
		if (!mReducedStates.containsKey(key)) {
			mReducedStates.put(key, mStateFactory.intersection(key.getFirst(), key.getSecond()));
		}
		return mReducedStates.get(key);
	}

	private Pair<STATE, STATE> getPair(final STATE q1, final STATE q2) {
		if (!mPairsMap.containsKey(q1)) {
			mPairsMap.put(q1, new HashMap<>());
		}
		if (!mPairsMap.get(q1).containsKey(q2)) {
			mPairsMap.get(q1).put(q2, new Pair<>(q1, q2));
		}
		return mPairsMap.get(q1).get(q2);
	}

	@Override
	public String startMessage() {
		return "Start intersection tree automatons";
	}

	@Override
	public String exitMessage() {
		return "Exit intersection tree automatons";
	}

	private TreeAutomatonBU<LETTER, STATE> computeResult() {
		// Minimal states intersection.
		//final TreeAutomatonBU<LETTER, Pair<STATE, STATE>> res = new TreeAutomatonBU<>();

		//res.extendAlphabet(mTreeA.getAlphabet());
		//res.extendAlphabet(mTreeB.getAlphabet());

		final Set<LETTER> alphabet = new HashSet<>();
		final Set<Pair<STATE, STATE>> finalStates = new HashSet<>();
		final Set<TreeAutomatonRule<LETTER, Pair<STATE, STATE>>> newRules = new HashSet<>();
		alphabet.addAll(mTreeA.getAlphabet());
		alphabet.addAll(mTreeB.getAlphabet());

		final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> symbolToRuleA = new HashMap<>();
		final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> symbolToRuleB = new HashMap<>();

		for (final List<STATE> src : mTreeA.getSourceCombinations()) {
			for (final TreeAutomatonRule<LETTER, STATE> ruleA : mTreeA.getSuccessors(src)) {
				Collection<TreeAutomatonRule<LETTER, STATE>> rules;
				if (symbolToRuleA.containsKey(ruleA.getLetter())) {
					rules = symbolToRuleA.get(ruleA.getLetter());
				} else {
					rules = new LinkedList<>();
					symbolToRuleA.put(ruleA.getLetter(), rules);
				}
				rules.add(ruleA);
			}
		}
		for (final List<STATE> src : mTreeB.getSourceCombinations()) {
			for (final TreeAutomatonRule<LETTER, STATE> ruleB : mTreeB.getSuccessors(src)) {
				Collection<TreeAutomatonRule<LETTER, STATE>> rules;
				if (symbolToRuleB.containsKey(ruleB.getLetter())) {
					rules = symbolToRuleB.get(ruleB.getLetter());
				} else {
					rules = new LinkedList<>();
					symbolToRuleB.put(ruleB.getLetter(), rules);
				}
				rules.add(ruleB);
			}
		}

		for (final LETTER letter : symbolToRuleA.keySet()) {
			if (symbolToRuleB.containsKey(letter)) {
				for (final TreeAutomatonRule<LETTER, STATE> ruleA : symbolToRuleA.get(letter)) {
					for (final TreeAutomatonRule<LETTER, STATE> ruleB : symbolToRuleB.get(letter)) {
						if (ruleA.getArity() == ruleB.getArity()) {
							final List<Pair<STATE, STATE>> source = new ArrayList<>();
							final int ar = ruleA.getArity();
							for (int i = 0; i < ar; ++i) {
								source.add(getPair(ruleA.getSource().get(i), ruleB.getSource().get(i)));
							}
							final Pair<STATE, STATE> dest = getPair(ruleA.getDest(), ruleB.getDest());
							newRules.add(new TreeAutomatonRule<>(letter, source, dest));
							//res.addRule(new TreeAutomatonRule<>(letter, source, dest));
						}
					}
				}
			}
		}
		for (final STATE q1 : mPairsMap.keySet()) {
			for (final STATE q2 : mPairsMap.get(q1).keySet()) {
				final Pair<STATE, STATE> st = getPair(q1, q2);

				if (mTreeA.isFinalState(q1) && mTreeB.isFinalState(q2)) {
					finalStates.add(st);
					//res.addFinalState(st);
				}
			}
		}

		final TreeAutomatonBU<LETTER, STATE> reducedResult = new TreeAutomatonBU<>();

		for (final TreeAutomatonRule<LETTER, Pair<STATE, STATE>> rule : newRules) {
			final List<STATE> src = new ArrayList<>();
			for (final Pair<STATE, STATE> pr : rule.getSource()) {
				src.add(reduceState(pr));
			}
			reducedResult.addRule(new TreeAutomatonRule<>(rule.getLetter(), src, reduceState(rule.getDest())));
		}

		for (final Pair<STATE, STATE> state : finalStates) {
			reducedResult.addFinalState(reduceState(state));
		}
		/*
		for (final Pair<STATE, STATE> state : res.getStates()) {
			reducedResult.addState(reduceState(state));
			if (res.isFinalState(state)) {
				reducedResult.addFinalState(reduceState(state));
			}
		}
		*/

		return reducedResult;
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
