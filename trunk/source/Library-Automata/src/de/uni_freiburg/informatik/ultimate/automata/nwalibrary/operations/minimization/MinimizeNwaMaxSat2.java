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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat2.MaxHornSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat2.MaxHornSatSolver.VariableStatus;
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
 * MAX-SAT based minimization for NWAs.
 * This operation is a re-implementation of Jens' bachlor thesis.
 * Its main purpose is to test the {@link MaxHornSatSolver}. For small 
 * determinstic NWAs it should produce small results efficiently.
 * For larger NWAs it runs out of memory. For nondeterministic NWAs it should
 * be correct, however the size reduction will be very poor for states with
 * nondeterministic outgoing transitions. (Given a pair of states q1, q2 and
 * a letter x, then q1 and q2 are only equivalent if all x-successors of q1
 * are equivalent to all x-successors of q2.)
 *  
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 */
public class MinimizeNwaMaxSat2<LETTER, STATE> extends AMinimizeNwa<LETTER, STATE>  
										implements IOperation<LETTER,STATE> {
	
	private final NestedMap2<STATE, STATE, Doubleton<STATE>> mStatePairs = new NestedMap2<>();
	private final MaxHornSatSolver<Doubleton<STATE>> mSolver = 
			new MaxHornSatSolver<Doubleton<STATE>>(mServices);
	private final Set<Doubleton<STATE>> mProcessedDoubletons = new HashSet<>();
	private final NestedWordAutomaton<LETTER, STATE> mResult;
	private final Collection<Set<STATE>> mInitialEquivalenceClasses;
	private final Map<STATE, Set<STATE>> mState2EquivalenceClass;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private int mNumberClauses_Acceptance = 0;
	private int mNumberClauses_Transitions = 0;
	private int mNumberClauses_Transitivity = 0;
	
	public MinimizeNwaMaxSat2(AutomataLibraryServices services, StateFactory<STATE> stateFactory,
			IDoubleDeckerAutomaton<LETTER, STATE> operand, final boolean addMapOldState2newState)
					throws AutomataLibraryException {
		super(services, stateFactory, "minimizeNwaMaxSat2", operand);
		mOperand = operand;
//		if (!new IsDeterministic<>(mServices, operand).getResult()) {
//		throw new AssertionError("not deterministic");
//	}
		mInitialEquivalenceClasses = 
				(new LookaheadPartitionConstructor<LETTER, STATE>(mServices, mOperand)).getResult();
		mState2EquivalenceClass = new HashMap<>();
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			for (final STATE state : equivalenceClass) {
				mState2EquivalenceClass.put(state, equivalenceClass);
			}
		}
		generateVariables();
		generateTransitionConstraints();
		generateTransitivityConstraints();
		mLogger.info("Number of clauses for acceptance: " + mNumberClauses_Acceptance
				+ " Number of clauses for transitions: " + mNumberClauses_Transitions
				+ " Number of clauses for transitivity: " + mNumberClauses_Transitivity
				);
		final boolean satisfiable = mSolver.solve();
		if (!satisfiable) {
			throw new AssertionError("Constructed constraints were unsatisfiable");
		}
		final UnionFind<STATE> resultingEquivalenceClasses = constructEquivalenceClasses();
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor = 
				new QuotientNwaConstructor<>(mServices, mStateFactory, mOperand,
						resultingEquivalenceClasses, addMapOldState2newState);
		mResult = quotientNwaConstructor.getResult();
	}
	
	public MinimizeNwaMaxSat2(AutomataLibraryServices services, StateFactory<STATE> stateFactory,
			IDoubleDeckerAutomaton<LETTER, STATE> operand) throws AutomataLibraryException {
		this(services, stateFactory, operand, false);
	}
	
	private boolean haveSimilarEquivalenceClass(STATE inputState1, STATE inputState2) {
		return mState2EquivalenceClass.get(inputState1) == mState2EquivalenceClass.get(inputState2);
	}
	
	private STATE[] constructStateArray(Collection<STATE> states) {
		return states.toArray((STATE[]) new Object[states.size()]);
	}

	private UnionFind<STATE> constructEquivalenceClasses() throws AssertionError {
		final UnionFind<STATE> resultingEquivalenceClasses;
		resultingEquivalenceClasses = new UnionFind<>();
		for (final Entry<Doubleton<STATE>, Boolean> entry : mSolver.getValues().entrySet()) {
			if (entry.getValue() == null) {
				throw new AssertionError("value not determined " + entry.getKey());
			}
			if (entry.getValue()) {
				final STATE rep1 = resultingEquivalenceClasses.findAndConstructEquivalenceClassIfNeeded(
						entry.getKey().getOneElement());
				final STATE rep2 = resultingEquivalenceClasses.findAndConstructEquivalenceClassIfNeeded(
						entry.getKey().getOtherElement());
				resultingEquivalenceClasses.union(rep1, rep2);
			} else {
				// do nothing
			}
		}
		return resultingEquivalenceClasses;
	}

	private void generateVariables() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i=0; i<states.length; i++) {
				for (int j=0; j<i; j++) {
					final Doubleton<STATE> doubleton = new Doubleton<STATE>(states[i], states[j]);
					mStatePairs.put(states[i], states[j], doubleton);
					mStatePairs.put(states[j], states[i], doubleton);
					mSolver.addVariable(doubleton);
					if (mOperand.isFinal(states[i]) ^ mOperand.isFinal(states[j])) {
						mSolver.addHornClause(consArr(doubleton), null);
						mNumberClauses_Acceptance++;
					}
				}
			}
			checkTimeout();
		}
	}
	
	private void generateTransitionConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i=0; i<states.length; i++) {
				for (int j=0; j<i; j++) {
					if (knownToBeDifferent(states[i], states[j])) {
						// all corresponding clauses are trivially true
						continue;
					}
					final boolean predPairKnowToBeSimilar = knownToBeSimilar(states[i], states[j]);

					final STATE state1 = states[i];
					final STATE state2 = states[j];

					generateTransitionConstraint_Internal(state1, state2, predPairKnowToBeSimilar);
					generateTransitionConstraint_Call(state1, state2, predPairKnowToBeSimilar);

					for (final STATE downi : mOperand.getDownStates(states[i])) {
						for (final STATE downj : mOperand.getDownStates(states[j])) {
							generateTransitionConstraint_Return(state1, state2, 
									predPairKnowToBeSimilar, downi, downj);
						}
					}
				}
				final STATE[] downStates = constructStateArray(mOperand.getDownStates(states[i]));
				for (int k=0; k<downStates.length; k++) {
					for (int l=0; l<k; l++) {
						generateTransitionConstraint_Return(states[i], states[i], 
								true, downStates[k], downStates[l]);
					}
				}
				checkTimeout();
			}
		}
	}

	private void generateTransitionConstraint_Internal(STATE predState1,
			STATE predState2, boolean predPairKnowToBeSimilar) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans1 : mOperand.internalSuccessors(predState1)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans2 : mOperand.internalSuccessors(
					predState2, trans1.getLetter())) {
				final STATE succState1 = trans1.getSucc();
				final STATE succState2 = trans2.getSucc();
				generateTernaryTransitionConstraint(predState1, predState2,
						predPairKnowToBeSimilar, succState1, succState2);
			}
		}
	}
	
	private void generateTransitionConstraint_Call(STATE predState1,
			STATE predState2, boolean predPairKnowToBeSimilar) {
		for (final OutgoingCallTransition<LETTER, STATE> trans1 : mOperand.callSuccessors(predState1)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans2 : mOperand.callSuccessors(
					predState2, trans1.getLetter())) {
				final STATE succState1 = trans1.getSucc();
				final STATE succState2 = trans2.getSucc();
				generateTernaryTransitionConstraint(predState1, predState2,
						predPairKnowToBeSimilar, succState1, succState2);
			}
		}
	}
	
	private void generateTransitionConstraint_Return(STATE linPredState1,
			STATE linPredState2, boolean linPredPairKnowToBeSimilar,
			STATE hierPredState1, STATE hierPredState2) {
		if (knownToBeDifferent(hierPredState1, hierPredState2)) {
			// all corresponding clauses are trivially true
			return;
		}
		final Doubleton<STATE> predDoubleton;
		if (linPredPairKnowToBeSimilar) {
			// we will not need it
			predDoubleton = null;
		} else {
			predDoubleton= mStatePairs.get(linPredState1, linPredState2); 
		}
		final boolean hierPredPairKnowToBeSimilar = knownToBeSimilar(hierPredState1, hierPredState2);
		final Doubleton<STATE> hierPredDoubleton;
		if (hierPredPairKnowToBeSimilar) {
			// we will not need it
			hierPredDoubleton = null;
		} else {
			hierPredDoubleton= mStatePairs.get(hierPredState1, hierPredState2); 
		}
		if (linPredPairKnowToBeSimilar && hierPredPairKnowToBeSimilar) {
			throw new AssertionError("both can't be similar");
		}
		if (!haveSameOutgoingReturnSymbols(linPredState1, hierPredState1, linPredState2, hierPredState2)) {
			addThreeLiteralHornClause(predDoubleton, hierPredDoubleton, null);
		} else {
			// both DoubleDeckers have same outgoing return symbols
			for (final OutgoingReturnTransition<LETTER, STATE> trans1 : mOperand.returnSuccessorsGivenHier(
					linPredState1, hierPredState1)) {
				for (final OutgoingReturnTransition<LETTER, STATE> trans2 : mOperand.returnSucccessors(
						linPredState2, hierPredState2, trans1.getLetter())) {
					if (knownToBeSimilar(trans1.getSucc(), trans2.getSucc())) {
						// corresponding clauses is trivially true
						continue;
					}
					final Doubleton<STATE> succDoubleton;
					if (knownToBeDifferent(trans1.getSucc(), trans2.getSucc())) {
						succDoubleton = null;
					} else {
						succDoubleton = mStatePairs.get(trans1.getSucc(), trans2.getSucc());
					}
					addThreeLiteralHornClause(predDoubleton, hierPredDoubleton, succDoubleton);
				}
			}
		}
	}

	private void generateTernaryTransitionConstraint(STATE predState1, STATE predState2,
			boolean predPairKnowToBeSimilar, final STATE succState1, final STATE succState2) {
		if (knownToBeSimilar(succState1, succState2)) {
			return;
		}
		final Doubleton<STATE> predDoubleton;
		if (predPairKnowToBeSimilar) {
			// we will not need it
			predDoubleton = null;
		} else {
			predDoubleton= mStatePairs.get(predState1, predState2); 
		}
		final Doubleton<STATE> succDoubleton;
		if (knownToBeDifferent(succState1, succState2)) {
			succDoubleton = null;
		} else {
			succDoubleton = mStatePairs.get(succState1, succState2);
		}
		addTwoLiteralHornClause(predDoubleton, succDoubleton);
	}
	
	private void addTwoLiteralHornClause(Doubleton<STATE> negativeAtom, Doubleton<STATE> positiveAtom) {
		if (negativeAtom == null) {
			if (positiveAtom == null) {
				throw new AssertionError("clause must not be empty");
			} else {
				mSolver.addHornClause(new Doubleton[0], positiveAtom);
				mNumberClauses_Transitions++;
			}
		} else {
			mSolver.addHornClause(consArr(negativeAtom), positiveAtom);
			mNumberClauses_Transitions++;
		}
	}
	
	private void addThreeLiteralHornClause(Doubleton<STATE> negativeAtom1, Doubleton<STATE> negativeAtom2, 
			Doubleton<STATE> positiveAtom) {
		if (negativeAtom1 == null) {
			addTwoLiteralHornClause(negativeAtom2, positiveAtom);
		} else if (negativeAtom2 == null) {
			addTwoLiteralHornClause(negativeAtom1, positiveAtom);
		} else {
			mSolver.addHornClause(consArr(negativeAtom1, negativeAtom2), positiveAtom);
			mNumberClauses_Transitions++;
		}
	}

	
	private boolean haveSameOutgoingReturnSymbols(STATE up1, STATE down1, STATE up2, STATE down2) {
		final Set<LETTER> returnLetters1 = new HashSet<>();
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessorsGivenHier(up1, down1)) {
			returnLetters1.add(trans.getLetter());
		}
		final Set<LETTER> returnLetters2 = new HashSet<>();
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessorsGivenHier(up2, down2)) {
			returnLetters2.add(trans.getLetter());
		}
		return returnLetters1.equals(returnLetters2);
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
		final Doubleton<STATE> doubleton = mStatePairs.get(inputState1, inputState2);
		final Boolean value = mSolver.getValues().get(doubleton);
		return (value != null) && !value;
	}
	
	private boolean solverSaysSimilar(STATE inputState1, STATE inputState2) {
		assert haveSimilarEquivalenceClass(inputState1, inputState2) : "check not available";
		final Doubleton<STATE> doubleton = mStatePairs.get(inputState1, inputState2);
		final Boolean value = mSolver.getValues().get(doubleton);
		return (value != null) && !value;
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
	
	private void generateTransitivityConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i=0; i<states.length; i++) {
				for (int j=0; j<i; j++) {
					//TODO: use already computed solver information to save some time
					// will not safe much, because solver does this quickly
					for (int k=0; k<j; k++) {
						final Doubleton<STATE> doubleton_ij = mStatePairs.get(states[i], states[j]);
						final Doubleton<STATE> doubleton_jk = mStatePairs.get(states[j], states[k]);
						final Doubleton<STATE> doubleton_ik = mStatePairs.get(states[i], states[k]);
						mSolver.addHornClause(consArr(doubleton_ij, doubleton_jk), doubleton_ik);
						mSolver.addHornClause(consArr(doubleton_jk, doubleton_ik), doubleton_ij);
						mSolver.addHornClause(consArr(doubleton_ik, doubleton_ij), doubleton_jk);
						mNumberClauses_Transitivity = mNumberClauses_Transitivity + 3;
					}
					checkTimeout();
				}
			}
		}
	}


	private Doubleton<STATE>[] consArr(Doubleton<STATE>... doubletons) {
		return doubletons;
	}
	
	private Doubleton<STATE>[] consArr(Collection<Doubleton<STATE>> doubletons) {
		return doubletons.toArray(new Doubleton[doubletons.size()]);
	}

	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		return mResult;
	}
	
	private void checkTimeout() throws AutomataOperationCanceledException {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}
	}

}
