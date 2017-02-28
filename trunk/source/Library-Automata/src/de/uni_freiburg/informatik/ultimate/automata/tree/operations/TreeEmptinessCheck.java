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

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;

/**
 * Check emptiness of a tree automaton. The output is TreeRun.
 * 
 * @author Mostafa M. Amin <mostafa.amin93@gmail.com>
 *
 * @param <R>
 *            letter class of tree automaton.
 * @param <S>
 *            state class of tree automaton.
 */
public class TreeEmptinessCheck<R, S> implements IOperation<R, S, IStateFactory<S>> {

	private final ITreeAutomatonBU<R, S> mTreeAutomaton;
	protected final TreeRun<R, S> mResult;

	/***
	 * TreeEmptiness checker
	 * @param services
	 * @param tree
	 */
	public TreeEmptinessCheck(final AutomataLibraryServices services, final TreeAutomatonBU<R, S> tree) {
		mTreeAutomaton = tree;
		mResult = computeResult();
	}

	@Override
	public String operationName() {
		return "Emptiness";
	}

	@Override
	public String startMessage() {
		return "Starting emptiness check";
	}

	@Override
	public String exitMessage() {
		return "Exit emptiness check";
	}

	/***
	 * compute the emptiness check.
	 * @return
	 */
	private TreeRun<R, S> computeResult() {
		final LinkedList<TreeAutomatonRule<R, S>> worklist = new LinkedList<>();

		final Map<S, Collection<TreeAutomatonRule<R, S>>> rulesBySource = new HashMap<>();

		final Map<S, TreeRun<R, S>> soltree = new HashMap<>();

		for (final S init : mTreeAutomaton.getInitialStates()) {
			soltree.put(init, new TreeRun<R, S>(init));
		}
		for (final TreeAutomatonRule<R, S> rule : mTreeAutomaton.getRules()) {
			boolean initialRules = true;

			for (final S sourceState : rule.getSource()) {
				initialRules &= mTreeAutomaton.isInitialState(sourceState);

				Collection<TreeAutomatonRule<R, S>> sourceRules;
				if (rulesBySource.containsKey(sourceState)) {
					sourceRules = rulesBySource.get(sourceState);
				} else {
					sourceRules = new LinkedList<>();
					rulesBySource.put(sourceState, sourceRules);
				}
				sourceRules.add(rule);
			}
			if (initialRules) {
				worklist.add(rule);
			}
		}

		while (!worklist.isEmpty()) {
			final TreeAutomatonRule<R, S> rule = worklist.poll();
			final S dest = rule.getDest();

			final List<TreeRun<R, S>> subTrees = new LinkedList<>();
			if (soltree.containsKey(dest)) {
				// Already computed.
				continue;
			}

			boolean allMarked = true;
			for (final S q : rule.getSource()) {
				if (!soltree.containsKey(q)) {
					allMarked = false;
					break;
				}
				subTrees.add(soltree.get(q));
			}
			if (allMarked) {
				final TreeRun<R, S> newTree = new TreeRun<>(dest, rule.getLetter(), subTrees);
				soltree.put(dest, newTree);
				if (mTreeAutomaton.isFinalState(dest)) {
					return newTree;
				}
				if (rulesBySource.containsKey(dest)) {
					worklist.addAll(rulesBySource.get(dest));
					// worklist.pushAll(considerNext); // depth first
				}
			}

		}
		return null;
	}

	@Override
	public TreeRun<R, S> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<S> stateFactory) throws AutomataLibraryException {
		return false;
	}
}
