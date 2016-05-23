/*
 * Copyright (C) 2016 Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * Copyright (C) 2016 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat2.MaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat2.MaxSatSolver.VariableStatus;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * 
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 */
public class MinimizeNwaMaxSat2<LETTER, STATE> extends AMinimizeNwa<LETTER, STATE>  
										implements IOperation<LETTER,STATE> {
	
	private final NestedMap2<STATE, STATE, Doubleton<STATE>> m_StatePairs = new NestedMap2<>();
	private final MaxSatSolver<Doubleton<STATE>> m_Solver = new MaxSatSolver<>();
	private final Set<Doubleton<STATE>> m_ProcessedDoubletons = new HashSet<>();
	private final NestedWordAutomaton<LETTER, STATE> m_Result;
	private final Collection<Set<STATE>> m_EquivalenceClasses;
	private final Map<STATE, Set<STATE>> m_State2EquivalenceClass;
	private final IDoubleDeckerAutomaton<LETTER, STATE> m_Operand;

	public MinimizeNwaMaxSat2(AutomataLibraryServices services, StateFactory<STATE> stateFactory,
			IDoubleDeckerAutomaton<LETTER, STATE> operand) {
		super(services, stateFactory, "minimizeNwaMaxSat2", operand);
		m_Operand = operand;
		m_EquivalenceClasses = (new LookaheadPartitionConstructor<LETTER, STATE>(m_Services, m_operand)).getResult();
		m_State2EquivalenceClass = new HashMap<>();
		for (Set<STATE> equivalenceClass : m_EquivalenceClasses) {
			for (STATE state : equivalenceClass) {
				m_State2EquivalenceClass.put(state, equivalenceClass);
			}
		}
		m_Result = doBuildFormulas();
	}
	
	private boolean haveSimilarEquivalenceClass(STATE inputState1, STATE inputState2) {
		return m_State2EquivalenceClass.get(inputState1) == m_State2EquivalenceClass.get(inputState2);
	}
	
	private STATE[] constructStateArray(Collection<STATE> states) {
		return states.toArray((STATE[]) new Object[states.size()]);
	}

	private NestedWordAutomaton<LETTER, STATE> doBuildFormulas() {
		ArrayDeque<Doubleton<STATE>> worklist = new ArrayDeque<>();
		generateVariables(worklist);
		while (!worklist.isEmpty()) {
			Doubleton<STATE> doubleton = worklist.removeFirst();
			processDoubleton(doubleton, worklist);
		}
		generateTransitivityConstraints();
		m_Solver.solve();
		final UnionFind<STATE> uf = new UnionFind<>();
		for (Entry<Doubleton<STATE>, VariableStatus> entry : m_Solver.getValues().entrySet()) {
			switch (entry.getValue()) {
			case TRUE:
				final STATE rep1 = uf.findAndConstructEquivalenceClassIfNeeded(
						entry.getKey().getOneElement());
				final STATE rep2 = uf.findAndConstructEquivalenceClassIfNeeded(
						entry.getKey().getOtherElement());
				uf.union(rep1, rep2);
				break;
			case FALSE:
				// do nothing
				break;
			case UNSET:
				throw new AssertionError("value not determined " + entry.getKey());
			default:
				throw new AssertionError("unknown value " + entry.getKey());
			}
		}
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor = 
				new QuotientNwaConstructor<>(m_Services, m_StateFactory, m_operand, uf);
		return quotientNwaConstructor.getResult();
	}

	private void processDoubleton(Doubleton<STATE> doubleton, ArrayDeque<Doubleton<STATE>> worklist) {
		STATE one = doubleton.getOneElement();
		STATE other = doubleton.getOtherElement();
		// internal
		for (IncomingInternalTransition<LETTER, STATE> trans1 : m_operand.internalPredecessors(one)) {
			for (IncomingInternalTransition<LETTER, STATE> trans2 : m_operand.internalPredecessors(trans1.getLetter(), other)) {
				if (!trans1.getPred().equals(trans2.getPred())) {
					final Doubleton<STATE> predDoubleton = m_StatePairs.get(trans1.getPred(), trans2.getPred());
					if (!m_ProcessedDoubletons.contains(predDoubleton)) {
						worklist.add(predDoubleton);
						m_ProcessedDoubletons.add(predDoubleton);
					}
					m_Solver.addHornClause(consArr(predDoubleton), doubleton);
				}
			}
		}
		// call
		for (IncomingCallTransition<LETTER, STATE> trans1 : m_operand.callPredecessors(one)) {
			for (IncomingCallTransition<LETTER, STATE> trans2 : m_operand.callPredecessors(trans1.getLetter(), other)) {
				if (!trans1.getPred().equals(trans2.getPred())) {
					final Doubleton<STATE> predDoubleton = m_StatePairs.get(trans1.getPred(), trans2.getPred());
					if (!m_ProcessedDoubletons.contains(predDoubleton)) {
						worklist.add(predDoubleton);
						m_ProcessedDoubletons.add(predDoubleton);
					}
					m_Solver.addHornClause(consArr(predDoubleton), doubleton);
				}
			}
		}
		
		// return
		for (IncomingReturnTransition<LETTER, STATE> trans1 : m_operand.returnPredecessors(one)) {
			for (IncomingReturnTransition<LETTER, STATE> trans2 : m_operand.returnPredecessors(trans1.getLetter(), other)) {
				final Doubleton<STATE> linPredDoubleton = m_StatePairs.get(trans1.getLinPred(), trans2.getLinPred());
				final Doubleton<STATE> hierPredDoubleton = m_StatePairs.get(trans1.getHierPred(), trans2.getHierPred());
				if (!trans1.getLinPred().equals(trans2.getLinPred())) {
					assert linPredDoubleton != null;
					if (!m_ProcessedDoubletons.contains(linPredDoubleton)) {
						worklist.add(linPredDoubleton);
						m_ProcessedDoubletons.add(linPredDoubleton);
					}
					if (!trans1.getHierPred().equals(trans2.getHierPred())) {
						assert hierPredDoubleton != null;
						m_Solver.addHornClause(consArr(linPredDoubleton, hierPredDoubleton), doubleton);
					} else {
						assert hierPredDoubleton == null;
						m_Solver.addHornClause(consArr(linPredDoubleton), doubleton);
					}
				} else {
					if (!trans1.getHierPred().equals(trans2.getHierPred())) {
						assert hierPredDoubleton != null;
						m_Solver.addHornClause(consArr(hierPredDoubleton), doubleton);
					} else {
						assert hierPredDoubleton == null;
						// add nothing
					}
				}
			}
		}


		
	}

	private void generateVariables(ArrayDeque<Doubleton<STATE>> worklist) {
		for (Set<STATE> equivalenceClass : m_EquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i=0; i<states.length; i++) {
				for (int j=0; j<i; j++) {
					Doubleton<STATE> doubleton = new Doubleton<STATE>(states[i], states[j]);
					m_StatePairs.put(states[i], states[j], doubleton);
					m_StatePairs.put(states[j], states[i], doubleton);
					m_Solver.addVariable(doubleton);
//					worklist.add(doubleton);
//					m_ProcessedDoubletons.add(doubleton);
					if (m_operand.isFinal(states[i]) ^ m_operand.isFinal(states[j])) {
						m_Solver.addHornClause(consArr(doubleton), null);
					}
				}
			}
		}
	}
	
	private void generateTransitionConstraints() {
		for (Set<STATE> equivalenceClass : m_EquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i=0; i<states.length; i++) {
				for (int j=0; j<i; j++) {
					if (knownToBeDifferent(states[i], states[j])) {
						// all corresponding clauses are trivially true
						continue;
					}
					boolean predPairKnowToBeSimilar = knownToBeSimilar(states[i], states[j]);
					final Doubleton<STATE> predDoubleton;
					if (predPairKnowToBeSimilar) {
						// we will not need it
						predDoubleton = null;
					} else {
						predDoubleton= m_StatePairs.get(states[i], states[j]); 
					}

					for (OutgoingInternalTransition<LETTER, STATE> trans1 : m_operand.internalSuccessors(states[i])) {
						for (OutgoingInternalTransition<LETTER, STATE> trans2 : m_operand.internalSuccessors(states[j], trans1.getLetter())) {
							if (knownToBeSimilar(trans1.getSucc(), trans2.getSucc())) {
								// corresponding clauses is trivially true
								continue;
							}
							if (knownToBeDifferent(trans1.getSucc(), trans2.getSucc())) {
								assert !predPairKnowToBeSimilar;
								m_Solver.addHornClause(consArr(predDoubleton), null);
							} else {
								final Doubleton<STATE> succDoubleton = m_StatePairs.get(trans1.getSucc(), trans2.getSucc());
								if (predPairKnowToBeSimilar) {
									m_Solver.addHornClause(new Doubleton[0], succDoubleton);
								} else {
									m_Solver.addHornClause(consArr(predDoubleton), succDoubleton);
								}
							}
						}
					}

					for (OutgoingCallTransition<LETTER, STATE> trans1 : m_operand.callSuccessors(states[i])) {
						for (OutgoingCallTransition<LETTER, STATE> trans2 : m_operand.callSuccessors(states[j], trans1.getLetter())) {
							if (knownToBeSimilar(trans1.getSucc(), trans2.getSucc())) {
								// corresponding clauses is trivially true
								continue;
							}
							if (knownToBeDifferent(trans1.getSucc(), trans2.getSucc())) {
								assert !predPairKnowToBeSimilar;
								m_Solver.addHornClause(consArr(predDoubleton), null);
							} else {
								final Doubleton<STATE> succDoubleton = m_StatePairs.get(trans1.getSucc(), trans2.getSucc());
								if (predPairKnowToBeSimilar) {
									m_Solver.addHornClause(new Doubleton[0], succDoubleton);
								} else {
									m_Solver.addHornClause(consArr(predDoubleton), succDoubleton);
								}
							}
						}
					}

					for (STATE downi : m_Operand.getDownStates(states[i])) {
						for (STATE downj : m_Operand.getDownStates(states[j])) {
							if (knownToBeDifferent(downi, downj)) {
								// all corresponding clauses are trivially true
								continue;
							}
							boolean hierPredPairKnowToBeSimilar = knownToBeSimilar(downi, downj);
							final Doubleton<STATE> hierPredDoubleton;
							if (predPairKnowToBeSimilar) {
								// we will not need it
								hierPredDoubleton = null;
							} else {
								hierPredDoubleton= m_StatePairs.get(downi, downj); 
							}
							List<Doubleton<STATE>> negativeAtoms = new ArrayList<>();
							if (!predPairKnowToBeSimilar) {
								negativeAtoms.add(predDoubleton);
							}
							if (!hierPredPairKnowToBeSimilar) {
								negativeAtoms.add(hierPredDoubleton);
							}
							if (predPairKnowToBeSimilar && hierPredPairKnowToBeSimilar) {
								throw new AssertionError("both can't be similar");
							}
							if (haveDifferentOutgoingReturnSymbols(states[i], downi, states[j], downj)) {
								m_Solver.addHornClause(consArr(negativeAtoms), null);
							} else {
								// both DoubleDeckers have same outgoing return symbols
								for (OutgoingReturnTransition<LETTER, STATE> trans1 : m_operand.returnSuccessorsGivenHier(states[i], downi)) {
									for (OutgoingReturnTransition<LETTER, STATE> trans2 : m_operand.returnSucccessors(states[j], downj, trans1.getLetter())) {
										if (knownToBeSimilar(trans1.getSucc(), trans2.getSucc())) {
											// corresponding clauses is trivially true
											continue;
										}
										if (knownToBeDifferent(trans1.getSucc(), trans2.getSucc())) {
											assert !predPairKnowToBeSimilar;
											m_Solver.addHornClause(consArr(negativeAtoms), null);
										} else {
											final Doubleton<STATE> succDoubleton = m_StatePairs.get(trans1.getSucc(), trans2.getSucc());
											m_Solver.addHornClause(consArr(negativeAtoms), succDoubleton);
										}
									}

								}
							}
						}
					}
				}
			}
		}
	}

	
	private boolean haveDifferentOutgoingReturnSymbols(STATE state, STATE downi, STATE state2, STATE downj) {
		// TODO Auto-generated method stub
		return false;
	}

	private boolean knownToBeDifferent(STATE inputState1, STATE inputState2) {
		if (haveSimilarEquivalenceClass(inputState1, inputState2)) {
			if (solverSaysDifferent(inputState1, inputState2)) {
				return true;
			} else {
				// we do not know the answer yet
				return false;
			}
		} else {
			return true;
		}
	}
	
	private boolean solverSaysDifferent(STATE inputState1, STATE inputState2) {
		assert haveSimilarEquivalenceClass(inputState1, inputState2) : "check not available";
		final Doubleton<STATE> doubleton = m_StatePairs.get(inputState1, inputState2);
		if (m_Solver.getValues().get(doubleton) == VariableStatus.FALSE) {
			return true;
		} else {
			// solver does not know the answer yet
			return false;
		}
	}
	
	private boolean solverSaysSimilar(STATE inputState1, STATE inputState2) {
		assert haveSimilarEquivalenceClass(inputState1, inputState2) : "check not available";
		final Doubleton<STATE> doubleton = m_StatePairs.get(inputState1, inputState2);
		if (m_Solver.getValues().get(doubleton) == VariableStatus.TRUE) {
			return true;
		} else {
			// solver does not know the answer yet
			return false;
		}
	}
	
	private boolean knownToBeSimilar(STATE inputState1, STATE inputState2) {
		if (inputState1.equals(inputState2)) {
			return true;
		} else {
			if (haveSimilarEquivalenceClass(inputState1, inputState2)) {
				if (solverSaysSimilar(inputState1, inputState2)) {
					return true;
				} else {
					// we do not know the answer yet
					return false;
				}
			} else {
				return false;
		}
		}
	}
	
	
	
	private void generateTransitivityConstraints() {
		for (Set<STATE> equivalenceClass : m_EquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i=0; i<states.length; i++) {
				for (int j=0; j<i; j++) {
					//TODO: use already computed solver information to save some time
					// will not safe much, because solver does this quickly
					for (int k=0; k<j; k++) {
						final Doubleton<STATE> doubleton_ij = m_StatePairs.get(states[i], states[j]);
						final Doubleton<STATE> doubleton_jk = m_StatePairs.get(states[j], states[k]);
						final Doubleton<STATE> doubleton_ik = m_StatePairs.get(states[i], states[k]);
						m_Solver.addHornClause(consArr(doubleton_ij, doubleton_jk), doubleton_ik);
					}
				}
			}
		}
	}


	private Doubleton<STATE>[] consArr(Doubleton<STATE>... doubletons) {
		return doubletons;
	}
	
	private Doubleton<STATE>[] consArr(Collection<Doubleton<STATE>> doubletons) {
		return doubletons.toArray((Doubleton<STATE>[]) new Object[doubletons.size()]);
	}

	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		return m_Result;
	}

}
