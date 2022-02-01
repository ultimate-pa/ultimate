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
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;

/**
 * Operation of a treeAutomaton accepts a given Run.
 * 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER>
 *            letter of the tree automaton.
 * @param <STATE>
 *            state of the tree automaton.
 */
public class Accepts<LETTER extends IRankedLetter, STATE> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final Tree<LETTER> mExample;
	private final Boolean mResult;

	/***
	 * Operator to check if accepting a given tree run by a given tree
	 * automaton.
	 * 
	 * @param services
	 * @param automaton
	 * @param run
	 */
	public Accepts(final AutomataLibraryServices services, final ITreeAutomatonBU<LETTER, STATE> automaton,
			final TreeRun<LETTER, STATE> run) {
		this(services, automaton, run.getTree());
	}

	/***
	 * Operator to check if accepting a given tree by a given tree automaton.
	 * 
	 * @param services
	 * @param automaton
	 * @param run
	 */
	public Accepts(final AutomataLibraryServices services, final ITreeAutomatonBU<LETTER, STATE> automaton,
			final Tree<LETTER> run) {
		mExample = run;
		mTreeAutomaton = automaton;
		mResult = computeResult();
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName();
	}

	@Override
	public String exitMessage() {
		return "Exit " + getOperationName();
	}

	/**
	 * 
	 * @param t a subtree
	 * @return Set of states that the automaton may be in after reading subtree t
	 */
	private Set<STATE> checkTree(final Tree<LETTER> t) {
		final ArrayList<Set<STATE>> statesReachableFromChildren = new ArrayList<>();
		for (final Tree<LETTER> ch : t.getChildren()) {
			Set<STATE> childResult = checkTree(ch);
			if (childResult.isEmpty()) {
				// one of the child subtrees does not have a derivation -- we can reject right here
				return Collections.emptySet();
			}
			statesReachableFromChildren.add(childResult);
		}
		
		final Iterable<TreeAutomatonRule<LETTER, STATE>> rulesForCurrentLetter = 
				mTreeAutomaton.getSuccessors(t.getSymbol());

		if (rulesForCurrentLetter == null) {
			// there is no rule we can go on with from the current letter
			return Collections.emptySet();
		}

		final Set<STATE> res = new HashSet<>();
		for (final TreeAutomatonRule<LETTER, STATE> rule : rulesForCurrentLetter) {
			assert rule.getArity() == statesReachableFromChildren.size();
			boolean validDerivation = true;
			for (int i = 0; i < rule.getArity(); ++i) {
				final STATE sr = rule.getSource().get(i);
				if (!statesReachableFromChildren.get(i).contains(sr)) {
					validDerivation = false;
					break;
				}
			}
			if (validDerivation) {
				res.add(rule.getDest());
			}
		}
		return res;
	}

	private Boolean computeResult() {
		final Set<STATE> derivations = checkTree(mExample);
		for (final STATE st : derivations) {
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
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO implement a meaningful check
		return true;
	}
}
