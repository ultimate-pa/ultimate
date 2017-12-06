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
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;

/**
 * Check emptiness of a tree automaton. The output is TreeRun.
 * 
 * @author Mostafa M. Amin <mostafa.amin93@gmail.com>
 *
 * @param <LETTER>
 *            letter class of tree automaton.
 * @param <STATE>
 *            state class of tree automaton.
 */
public class IsEmpty<LETTER extends IRankedLetter, STATE> extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	protected final TreeRun<LETTER, STATE> mResultTreeRun;

	/***
	 * TreeEmptiness checker
	 * @param services
	 * @param tree
	 */
	public IsEmpty(final AutomataLibraryServices services, final ITreeAutomatonBU<LETTER, STATE> tree) {
		super(services);
		mTreeAutomaton = tree;
		mResultTreeRun = computeResult();
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
	private TreeRun<LETTER, STATE> computeResult() {
		final LinkedList<TreeAutomatonRule<LETTER, STATE>> worklist = new LinkedList<>();

		final Map<STATE, Collection<TreeAutomatonRule<LETTER, STATE>>> rulesBySource = new HashMap<>();

		// maps a state s to a treeRun whose root can be labeled with s by mTreeAutomaton
		final Map<STATE, TreeRun<LETTER, STATE>> soltree = new HashMap<>();

		for (final List<STATE> src : mTreeAutomaton.getSourceCombinations()) {
			for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getSuccessors(src)) {
	
				for (final STATE sourceState : rule.getSource()) {
	
					Collection<TreeAutomatonRule<LETTER, STATE>> sourceRules;
					if (rulesBySource.containsKey(sourceState)) {
						sourceRules = rulesBySource.get(sourceState);
					} else {
						sourceRules = new LinkedList<>();
						rulesBySource.put(sourceState, sourceRules);
					}
					sourceRules.add(rule);
				}
				if (rule.getSource().isEmpty()) {
					// a rule with an empty source list is an "initial rule"
					worklist.add(rule);
				}
			}
		}

		while (!worklist.isEmpty()) {
			final TreeAutomatonRule<LETTER, STATE> rule = worklist.poll();
			final STATE dest = rule.getDest();

			if (soltree.containsKey(dest)) {
				// Already computed.
				continue;
			}

			final List<TreeRun<LETTER, STATE>> subTrees = new LinkedList<>();
			boolean allMarked = true;
			for (final STATE q : rule.getSource()) {
				if (!soltree.containsKey(q)) {
					allMarked = false;
					break;
				}
				subTrees.add(soltree.get(q));
			}
			if (allMarked) {
				final TreeRun<LETTER, STATE> newTree = new TreeRun<>(dest, rule.getLetter(), subTrees);
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
	public Boolean getResult() {
		return mResultTreeRun == null;
	}

	public TreeRun<LETTER, STATE> getTreeRun() {
		return mResultTreeRun;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
