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
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/**
 * Totalize TreeAutomaton operation
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class Totalize<LETTER extends IRankedLetter, STATE> extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>>
		implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final ISinkStateFactory<STATE> mStateFactory;

	protected final ITreeAutomatonBU<LETTER, STATE> mResult;
	private final Map<Integer, List<List<STATE>>> mMemCombinations;

	private final STATE mDummyState;
	private final Set<STATE> mStates;
	private final Collection<LETTER> mAlphabet;

	/***
	 * Totalize operation constructor
	 *
	 * @param services
	 * @param factory
	 * @param tree
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE>> Totalize(
			final AutomataLibraryServices services, final SF factory, final ITreeAutomatonBU<LETTER, STATE> tree) {
		super(services);
		mTreeAutomaton = new Determinize<>(services, factory, tree).getResult();
		mStateFactory = factory;
		mMemCombinations = new HashMap<>();
		mDummyState = mStateFactory.createSinkStateContent();
		mStates = new HashSet<>();
		mStates.add(mDummyState);
		mStates.addAll(mTreeAutomaton.getStates());
		mAlphabet = new HashSet<>();
		mAlphabet.addAll(tree.getAlphabet());
		mResult = computeTotalize();
	}

	/***
	 * Totalize operation constructor
	 *
	 * @param services
	 * @param factory
	 * @param tree The given tree automaton
	 * @param alphabet The given extra alphabet to include while totalization
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE>> Totalize(
			final AutomataLibraryServices services, final SF factory, final ITreeAutomatonBU<LETTER, STATE> tree,
			final Collection<LETTER> alphabet) {
		super(services);
		mTreeAutomaton = new Determinize<>(services, factory, tree).getResult();
		mStateFactory = factory;
		mMemCombinations = new HashMap<>();
		mDummyState = mStateFactory.createSinkStateContent();
		mStates = new HashSet<>();
		mStates.add(mDummyState);
		mStates.addAll(mTreeAutomaton.getStates());
		mAlphabet = new HashSet<>();
		mAlphabet.addAll(alphabet);
		mAlphabet.addAll(tree.getAlphabet());
		//((TreeAutomatonBU<LETTER, STATE>) mTreeAutomaton).extendAlphabet(mAlphabet);
		mResult = computeTotalize();
	}

	/***
	 * All possible Combinations of states of a given size
	 *
	 * @param siz
	 * @return
	 */
	private List<List<STATE>> combinations(final int siz) {
		if (mMemCombinations.containsKey(siz)) {
			return mMemCombinations.get(siz);
		}
		final ArrayList<List<STATE>> res = new ArrayList<>();
		if (siz == 0) {
			final ArrayList<STATE> st = new ArrayList<>();
			res.add(st);
			mMemCombinations.put(siz, res);
			return res;
		}
		final List<List<STATE>> subres = combinations(siz - 1);
		for (final STATE st : mStates) {
			for (final List<STATE> subst : subres) {
				final List<STATE> t = new ArrayList<>(subst.size());
				t.addAll(subst);
				t.add(st);
				res.add(t);
			}
		}
		mMemCombinations.put(siz, res);
		return res;
	}

	/***
	 * Compute the totalization result.
	 *
	 * @return
	 */
	private TreeAutomatonBU<LETTER, STATE> computeTotalize() {
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();

		res.extendAlphabet(mTreeAutomaton.getAlphabet());
		res.extendAlphabet(mAlphabet);
		for (final STATE st : mStates) {
			res.addState(st);
			if (mTreeAutomaton.isFinalState(st)) {
				res.addFinalState(st);
			}
		}
		for (final List<STATE> src : mTreeAutomaton.getSourceCombinations()) {
			for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getSuccessors(src)) {
				res.addRule(rule);
				for (final List<STATE> srcSt : combinations(rule.getArity())) {
					final Iterable<STATE> st = mTreeAutomaton.getSuccessors(srcSt, rule.getLetter());
					if (st == null || !st.iterator().hasNext()) {
						res.addRule(new TreeAutomatonRule<>(rule.getLetter(), srcSt, mDummyState));
					}
				}
				assert rule.getLetter().getRank() == rule.getArity();
			}
		}
		for (final LETTER sym : mAlphabet) {
			final int arity = sym.getRank();
			for (final List<STATE> srcSt : combinations(arity)) {
				final Iterable<STATE> st = mTreeAutomaton.getSuccessors(srcSt, sym);
				if (st == null || !st.iterator().hasNext()) {
					res.addRule(new TreeAutomatonRule<>(sym, srcSt, mDummyState));
				}
			}
		}
		return res;
	}

	@Override
	public String startMessage() {
		return "Starting " + getOperationName();
	}

	@Override
	public String exitMessage() {
		return "Finishing " + getOperationName();
	}

	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		assert new isTotal<>(mServices, mResult).getResult();
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}