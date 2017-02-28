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
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;

/**
 * Operation of a treeAutomaton accepts a given Run.
 * 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <R>
 *            letter of the tree automaton.
 * @param <S>
 *            state of the tree automaton.
 */
public class Accepts<R, S> implements IOperation<R, S, IStateFactory<S>> {
	private final TreeAutomatonBU<R, S> mTreeAutomaton;
	private final Tree<R> mExample;
	private final Boolean mResult;

	/***
	 * Operator to check if accepting a given tree run by a given tree automaton.
	 * @param services
	 * @param automaton
	 * @param run
	 */
	public Accepts(final AutomataLibraryServices services, final ITreeAutomatonBU<R, S> automaton,
			final TreeRun<R, S> run) {
		this(services, automaton, run.getTree());
	}
	
	/***
	 * Operator to check if accepting a given tree by a given tree automaton.
	 * @param services
	 * @param automaton
	 * @param run
	 */
	public Accepts(final AutomataLibraryServices services, final ITreeAutomatonBU<R, S> automaton,
			final Tree<R> run) {
		mExample = run;
		mTreeAutomaton = (TreeAutomatonBU<R, S>) automaton;
		mResult = computeResult();
	}

	@Override
	public String operationName() {
		return "TreeAccepts";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Exit " + operationName();
	}

	private Set<S> checkTree(final Tree<R> t) {
		final Set<S> res = new HashSet<>();

		final ArrayList<Set<S>> next = new ArrayList<>();
		for (final Tree<R> ch : t.getChildren()) {
			next.add(checkTree(ch));
		}

		final Iterable<TreeAutomatonRule<R, S>> st = mTreeAutomaton.getRulesByLetter(t.getSymbol());

		if (st == null) {
			return res;
		}
		for (final TreeAutomatonRule<R, S> rule : st) {
			if (rule.getSource().size() != next.size()) {
				continue;
			}
			for (int i = 0; i < next.size(); ++i) {
				final S sr = rule.getSource().get(i);
				if (!next.get(i).contains(sr) && !mTreeAutomaton.isInitialState(sr)) {
					continue;
				}
			}
			res.add(rule.getDest());
		}
		return res;
	}

	private Boolean computeResult() {
		final Set<S> derivations = checkTree(mExample);
		for (final S st : derivations) {
			if (mTreeAutomaton.isFinalState(st)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<S> stateFactory) throws AutomataLibraryException {
		// TODO implement a meaningful check
		return true;
	}
}
