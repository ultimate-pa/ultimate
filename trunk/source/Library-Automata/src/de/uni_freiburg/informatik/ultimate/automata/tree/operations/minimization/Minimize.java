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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Totalize;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.performance.SinkMergeIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.DisjointSets;

/**
 * Minimize a given treeAutomaton.
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <LETTER>
 *            letter of the tree automaton.
 * @param <STATE>
 *            state of the tree automaton.
 */
public class Minimize<LETTER extends IRankedLetter, STATE> extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>>
		implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final TreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final SinkMergeIntersectStateFactory<STATE> mStateFactory;

	protected final ITreeAutomatonBU<LETTER, STATE> mResult;

	private final Map<Set<STATE>, STATE> mMinimizedStates;

	/**
	 * The operand of this operation, i.e. the automaton to minimize.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mOperand;

	/***
	 * Constructor of Minimize operator
	 *
	 * @param services
	 * @param factory
	 * @param tree
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> Minimize(
			final AutomataLibraryServices services, final SF factory, final ITreeAutomatonBU<LETTER, STATE> tree) {
		super(services);
		this.mOperand = tree;
		mTreeAutomaton = (TreeAutomatonBU<LETTER, STATE>) new Totalize<>(services, factory, tree).getResult();
		mStateFactory = new SinkMergeIntersectStateFactory<>(factory, factory, factory);
		mMinimizedStates = new HashMap<>();
		mResult = computeResult();
	}

	private STATE minimize(final Set<STATE> st) {
		// minimize set of state to a new minimized state.
		if (!mMinimizedStates.containsKey(st)) {
			mMinimizedStates.put(st, mStateFactory.merge(st));
		}
		return mMinimizedStates.get(st);
	}

	@Override
	public String startMessage() {
		return "Starting " + getOperationName();
	}

	@Override
	public String exitMessage() {
		return "Exiting " + getOperationName();
	}

	/***
	 * Check if 2 states are replacable (equivalent)
	 *
	 * @param s1
	 * @param s2
	 * @param rule
	 * @param worklist
	 * @return
	 */
	private boolean replacable(final STATE s1, final STATE s2, final TreeAutomatonRule<LETTER, STATE> rule,
			final DisjointSets<STATE> worklist) {
		final ArrayList<STATE> src = new ArrayList<>();
		for (final STATE st : rule.getSource()) {
			src.add(st);
		}
		for (int idx = 0; idx < src.size(); ++idx) {
			if (src.get(idx) != s1) {
				continue;
			}
			@SuppressWarnings("unchecked")
			final ArrayList<STATE> s = (ArrayList<STATE>) src.clone();
			s.set(idx, s2);
			// If we replace an occurrence of s1 by s2 in the rule, and it still
			// yields an equivalent destination
			// Then we can replace s2 by s1 in this rule
			// TODO(amin): Check if just one occurrence or all of them is
			// needed.
			for (final STATE dest : mTreeAutomaton.getSuccessors(s, rule.getLetter())) {
				if (worklist.equiv(dest, rule.getDest())) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean replacable(final STATE s1, final STATE s2, final DisjointSets<STATE> partitions) {
		// If I can replace s1 by s2 in all rules of s1
		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRulesBySource(s1)) {
			if (!replacable(s1, s2, rule, partitions)) {
				return false;
			}
		}

		// If I can replace s2 by s1 in all rules of s2
		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRulesBySource(s2)) {
			if (!replacable(s2, s1, rule, partitions)) {
				return false;
			}
		}
		// Then both states are equivalent hence replaceable.
		return true;
	}

	private ITreeAutomatonBU<LETTER, STATE> computeResult() {
		// return removeUnreachables(mTreeAutomaton);

		DisjointSets<STATE> worklist = new DisjointSets<>(mTreeAutomaton.getStates());
		STATE finalState = null;
		STATE nonFinalState = null;
		for (final STATE state : mTreeAutomaton.getStates()) {
			if (mTreeAutomaton.isFinalState(state)) {
				if (finalState == null) {
					finalState = state;
				} else {
					// All final states are equivalent.
					worklist.union(finalState, state);
				}
			} else {
				if (nonFinalState == null) {
					nonFinalState = state;
				} else {
					worklist.union(nonFinalState, state);
				}
			}
		}
		DisjointSets<STATE> oldWorklist;
		do {
			oldWorklist = worklist;

			worklist = new DisjointSets<>(mTreeAutomaton.getStates());
			for (final Iterator<Set<STATE>> partitionsIt = oldWorklist.getParitionsIterator(); partitionsIt
					.hasNext();) {
				final Set<STATE> partition = partitionsIt.next();
				final ArrayList<STATE> states = new ArrayList<>();
				for (final Iterator<STATE> it = partition.iterator(); it.hasNext();) {
					states.add(it.next());
				}
				for (int i = 0; i < states.size(); ++i) {
					final STATE p1 = states.get(i);
					for (int j = 0; j < i; ++j) {
						// for each pair of states
						final STATE p2 = states.get(j);
						// if we can replace p1 and p2 together
						if (!oldWorklist.equiv(p1, p2) && replacable(p1, p2, oldWorklist)) {
							// then mark as equivalent
							worklist.union(p1, p2);
						}
					}
				}
			}
		} while (!worklist.equals(oldWorklist));

		// minimize all states
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();
		for (final STATE st : mTreeAutomaton.getStates()) {
			res.addState(minimize(worklist.getPartition(st)));
			if (mTreeAutomaton.isFinalState(st)) {
				res.addFinalState(minimize(worklist.getPartition(st)));
			}
		}

		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRules()) {
			final List<STATE> src = new ArrayList<>();
			// minimize all set of states in all rules.
			for (final STATE st : rule.getSource()) {
				src.add(minimize(worklist.getPartition(st)));
			}
			res.addRule(
					new TreeAutomatonRule<>(rule.getLetter(), src, minimize(worklist.getPartition(rule.getDest()))));
		}
		//return res;
		return removeUnreachables(res);

	}

	private ITreeAutomatonBU<LETTER, STATE> removeUnreachables(final TreeAutomatonBU<LETTER, STATE> treeAutomaton) {
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();

		final Set<STATE> worklist = new HashSet<>();

		final Set<STATE> oldWorklist = new HashSet<>();

		do {
			oldWorklist.addAll(worklist);

			for (final TreeAutomatonRule<LETTER, STATE> rule : treeAutomaton.getRules()) {
				// If the sources of this rule are reachable, then is the
				// destination.
				boolean allFound = true;
				for (final STATE sr : rule.getSource()) {
					if (!oldWorklist.contains(sr)) {
						allFound = false;
						break;
					}
				}
				if (allFound) {
					worklist.add(rule.getDest());
				}
			}
			// no new reachable states
		} while (!worklist.equals(oldWorklist));

		final Set<STATE> visited = new HashSet<>();
		// All reachable nodes from initial states.
		visited.addAll(worklist);

		worklist.clear();
		oldWorklist.clear();
		for (final STATE st : visited) {
			if (treeAutomaton.isFinalState(st)) {
				// needed final states.
				worklist.add(st);
			}
		}

		do {
			oldWorklist.addAll(worklist);

			for (final STATE dest : oldWorklist) {
				// for each needed state mark all it's predecessors as needed.
				final Map<LETTER, Iterable<List<STATE>>> prev = treeAutomaton.getPredecessors(dest);
				for (final LETTER symb : prev.keySet()) {
					for (final List<STATE> src : prev.get(symb)) {
						boolean allFound = true;
						for (final STATE st : src) {
							// If a final state has a never-reachable
							// predecessor, then this is an invalid rule.
							if (!visited.contains(st)) {
								allFound = false;
								break;
							}
						}
						if (allFound) {
							// Reachable Rule, Needed State
							res.addRule(new TreeAutomatonRule<>(symb, src, dest));
							// all source states are needed.
							worklist.addAll(src);
						}
					}
				}
			}
		} while (!worklist.equals(oldWorklist));

		for (final STATE st : worklist) {
			if (visited.contains(st)) {
				res.addState(st);
				if (treeAutomaton.isFinalState(st)) {
					res.addFinalState(st);
				}
			}
		}

		return res;
	}

	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.GeneralOperation#checkResult(de.
	 * uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory)
	 */
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// Check language equivalence between input and result automaton
		final IsEquivalent<LETTER, STATE> equivalenceCheck = new IsEquivalent<>(this.mServices, this.mStateFactory,
				this.mOperand, this.mResult);
		final boolean isEquivalent = equivalenceCheck.getResult().booleanValue();

		if (!isEquivalent && this.mLogger.isInfoEnabled()) {
			this.mLogger.info("Counterexample: " + equivalenceCheck.getCounterexample().get());
		}

		// TODO Also check whether the automaton is minimal
		return isEquivalent;
	}
}
