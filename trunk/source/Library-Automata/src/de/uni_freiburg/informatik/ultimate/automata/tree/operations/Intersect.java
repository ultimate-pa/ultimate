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
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Intersect 2 tree automatons.
 * 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <R>
 *            letter of the tree automatons.
 * @param <S>
 *            state of the tree automatons.
 */
public class Intersect<R, S> implements IOperation<R, S, IStateFactory<S>> {

	private final ITreeAutomatonBU<R, S> mTreeA;
	private final ITreeAutomatonBU<R, S> mTreeB;
	protected final ITreeAutomatonBU<R, S> mResult;

	private final IIntersectionStateFactory<S> mStateFactory;
	private final Map<S, Map<S, Pair<S, S>>> mPairsMap;
	private final Map<Pair<S, S>, S> mReducedStates;

	/**
	 * 
	 * NOTE: because of a convention in TestFileInterpreter, if an argument for the operation is a StateFactory, it must
	 * be the first argument same for Services, both: first services then StateFactory
	 * 
	 * @param services
	 * @param factory
	 * @param t1
	 * @param t2
	 */
	public Intersect(final AutomataLibraryServices services, final IIntersectionStateFactory<S> factory,
			final ITreeAutomatonBU<R, S> t1, final ITreeAutomatonBU<R, S> t2) {
		mReducedStates = new HashMap<>();
		mPairsMap = new HashMap<>();

		mStateFactory = factory;
		mTreeA = t1;
		mTreeB = t2;
		mResult = computeResult();
	}

	private S reduceState(final Pair<S, S> key) {
		if (!mReducedStates.containsKey(key)) {
			mReducedStates.put(key, mStateFactory.intersection(key.getFirst(), key.getSecond()));
		}
		return mReducedStates.get(key);
	}

	private Pair<S, S> getPair(final S q1, final S q2) {
		if (!mPairsMap.containsKey(q1)) {
			mPairsMap.put(q1, new HashMap<>());
		}
		if (!mPairsMap.get(q1).containsKey(q2)) {
			mPairsMap.get(q1).put(q2, new Pair<>(q1, q2));
		}
		return mPairsMap.get(q1).get(q2);
	}

	@Override
	public String operationName() {
		return "ta_intersect";
	}

	@Override
	public String startMessage() {
		return "Start intersection tree automatons";
	}

	@Override
	public String exitMessage() {
		return "Exit intersection tree automatons";
	}

	private TreeAutomatonBU<R, S> computeResult() {
		// Minimal states intersection.
		final TreeAutomatonBU<R, Pair<S, S>> res = new TreeAutomatonBU<>();

		res.extendAlphabet(mTreeA.getAlphabet());
		res.extendAlphabet(mTreeB.getAlphabet());

		final Map<R, Collection<TreeAutomatonRule<R, S>>> symbolToRuleA = new HashMap<>();
		final Map<R, Collection<TreeAutomatonRule<R, S>>> symbolToRuleB = new HashMap<>();

		for (final TreeAutomatonRule<R, S> ruleA : mTreeA.getRules()) {
			Collection<TreeAutomatonRule<R, S>> rules;
			if (symbolToRuleA.containsKey(ruleA.getLetter())) {
				rules = symbolToRuleA.get(ruleA.getLetter());
			} else {
				rules = new LinkedList<>();
				symbolToRuleA.put(ruleA.getLetter(), rules);
			}
			rules.add(ruleA);
		}
		for (final TreeAutomatonRule<R, S> ruleB : mTreeB.getRules()) {
			Collection<TreeAutomatonRule<R, S>> rules;
			if (symbolToRuleB.containsKey(ruleB.getLetter())) {
				rules = symbolToRuleB.get(ruleB.getLetter());
			} else {
				rules = new LinkedList<>();
				symbolToRuleB.put(ruleB.getLetter(), rules);
			}
			rules.add(ruleB);
		}

		for (final R letter : symbolToRuleA.keySet()) {
			if (symbolToRuleB.containsKey(letter)) {
				for (final TreeAutomatonRule<R, S> ruleA : symbolToRuleA.get(letter)) {
					for (final TreeAutomatonRule<R, S> ruleB : symbolToRuleB.get(letter)) {
						if (ruleA.getArity() == ruleB.getArity()) {
							final List<Pair<S, S>> source = new ArrayList<>();
							final int ar = ruleA.getArity();
							for (int i = 0; i < ar; ++i) {
								source.add(getPair(ruleA.getSource().get(i), ruleB.getSource().get(i)));
							}
							final Pair<S, S> dest = getPair(ruleA.getDest(), ruleB.getDest());
							res.addRule(new TreeAutomatonRule<>(letter, source, dest));
						}
					}
				}
			}
		}
		for (final S q1 : mPairsMap.keySet()) {
			for (final S q2 : mPairsMap.get(q1).keySet()) {
				final Pair<S, S> st = getPair(q1, q2);

				if (mTreeA.isInitialState(q1) && mTreeB.isInitialState(q2)) {
					res.addInitialState(st);
				}

				if (mTreeA.isFinalState(q1) && mTreeB.isFinalState(q2)) {
					res.addFinalState(st);
				}
			}
		}

		final TreeAutomatonBU<R, S> reducedResult = new TreeAutomatonBU<>();

		for (final TreeAutomatonRule<R, Pair<S, S>> rule : res.getRules()) {
			final List<S> src = new ArrayList<>();
			for (final Pair<S, S> pr : rule.getSource()) {
				src.add(reduceState(pr));
			}
			reducedResult.addRule(new TreeAutomatonRule<>(rule.getLetter(), src, reduceState(rule.getDest())));
		}

		for (final Pair<S, S> state : res.getStates()) {
			reducedResult.addState(reduceState(state));
			if (res.isInitialState(state)) {
				reducedResult.addInitialState(reduceState(state));
			}
			if (res.isFinalState(state)) {
				reducedResult.addFinalState(reduceState(state));
			}
		}

		return reducedResult;
	}

	@Override
	public ITreeAutomatonBU<R, S> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<S> stateFactory) throws AutomataLibraryException {
		// TODO: implement a meaningful check
		return true;
	}
}
