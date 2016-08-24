/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.GeneralMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.HornMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.TransitivityGeneralMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.VariableStatus;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * MAX-SAT based minimization for NWAs. This operation is a re-implementation of
 * Jens' bachelor thesis. Its main purpose is to test the
 * {@link HornMaxSatSolver}. For small deterministic NWAs it should produce small
 * results efficiently. For larger NWAs it runs out of memory. For
 * nondeterministic NWAs it should be correct, however the size reduction will
 * be very poor for states with nondeterministic outgoing transitions. (Given a
 * pair of states q1, q2 and a letter x, then q1 and q2 are only equivalent if
 * all x-successors of q1 are equivalent to all x-successors of q2.)
 * <p>
 * TODO For generating nondeterministic clauses, the order of the arguments
 * is not specified. Hence we might want to rearrange state1 and state2 such
 * that we have either few long clauses or many short clauses (for all types of
 * transitions).
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Tischner
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaMaxSat2<LETTER, STATE>
		extends AbstractMinimizeNwaDd<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	
	private final NestedMap2<STATE, STATE, Doubleton<STATE>> mStatePairs = new NestedMap2<>();
	private final AbstractMaxSatSolver<Doubleton<STATE>> mSolver;
	private final Collection<Set<STATE>> mInitialEquivalenceClasses;
	private final Map<STATE, Set<STATE>> mState2EquivalenceClass;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final boolean mUseFinalStateConstraints;
	private int mNumberClauses_Acceptance = 0;
	private int mNumberClauses_Transitions = 0;
	private int mNumberClauses_Transitions_Nondeterministic = 0;
	private int mNumberClauses_Transitivity = 0;
	/**
	 * This flag can also be set for nondeterministic automata.
	 * However, the results might not be satisfactory: all successors have to be
	 * be similar in this case.
	 */
	private final boolean mUseTransitionHornClauses;
	/**
	 * This flag indicates whether the new and more general solver should be
	 * used. The flag should only be set when dealing with deterministic
	 * transition clauses; otherwise the clauses are not of Horn form anymore.
	 * <p>
	 * TODO In the long term, we want to remove the old solver and hence this flag.
	 */
	private final boolean mUseHornSolver;
	
	/**
	 * Constructor that should be called by the automata script interpreter.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaMaxSat2(
			final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, true,
				new LookaheadPartitionConstructor<LETTER, STATE>(services, operand).getResult());
	}
	
	/**
	 * Constructor with an initial partition and option for backmapping.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param addMapOldState2newState
	 *            add map 'old state -> new state'
	 * @param initialEquivalenceClasses
	 *            We only try to merge states that are in one of the equivalence
	 *            classes
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaMaxSat2(
			final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final boolean addMapOldState2newState,
			final Collection<Set<STATE>> initialEquivalenceClasses)
			throws AutomataOperationCanceledException {
		/*
		 * TODO change fourth-to-last flag to 'false' to use the more general transition clauses
		 * <p>
		 * TODO change third-to-last flag to 'false' to use the more general solver
		 * <p>
		 * TODO change second-to-last flag to 'true' to use the transitivity on-the-fly
		 * <p>
		 * TODO change last flag to 'true' to use the transitivity on-the-fly with path compression
		 */
		this(services, stateFactory, operand, addMapOldState2newState,
				initialEquivalenceClasses, true, true, true, false, false);
	}
	
	/**
	 * Constructor that can be called by other classes of the automata library.
	 * It is not intended to be called by the automata script interpreter
	 * because there is too much input required.
	 * 
	 * @param addMapOldState2newState
	 *            add map 'old state -> new state'
	 * @param useFinalStateConstraints
	 *            add constraints that final and non-final states cannot be
	 *            merged
	 * @param initialEquivalenceClasses
	 *            We only try to merge states that are in one of the equivalence
	 *            classes
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param useTransitionHornClauses
	 *            use Horn clauses for transitions (preliminary results good for
	 *            nondeterministic automata)
	 * @param useHornSolver
	 *            use old Horn solver
	 * @param useTransitivityGenerator
	 *            use a transitivity generator
	 * @param usePathCompression
	 *            use path compression in the transitivity generator
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaMaxSat2(
			final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final boolean addMapOldState2newState,
			final Collection<Set<STATE>> initialEquivalenceClasses,
			final boolean useFinalStateConstraints,
			final boolean useTransitionHornClauses,
			final boolean useHornSolver,
			final boolean useTransitivityGenerator,
			final boolean usePathCompression)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, "minimizeNwaMaxSat2", operand);
		mOperand = operand;
		// if (!new IsDeterministic<>(mServices, operand).getResult()) {
		// throw new AssertionError("not deterministic");
		// }
		mUseFinalStateConstraints = useFinalStateConstraints;
		mInitialEquivalenceClasses = initialEquivalenceClasses;
		mUseTransitionHornClauses = useTransitionHornClauses;
		mUseHornSolver = useHornSolver;
		if (!mUseTransitionHornClauses && mUseHornSolver) {
			throw new IllegalArgumentException(
					"For using the Horn solver you must use Horn clauses.");
		}
		ScopedTransitivityGenerator<STATE> transitivityGenerator = null;
		if (mUseHornSolver) {
			mSolver = new HornMaxSatSolver<Doubleton<STATE>>(mServices);
		} else {
			if (useTransitivityGenerator) {
				transitivityGenerator = new ScopedTransitivityGenerator<>(usePathCompression);
				mSolver = new TransitivityGeneralMaxSatSolver<STATE>(mServices, transitivityGenerator);
			} else {
				mSolver = new GeneralMaxSatSolver<Doubleton<STATE>>(mServices);
			}
		}
		
		// TODO even copy an existing HashMap?
		mState2EquivalenceClass = new HashMap<>();
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			for (final STATE state : equivalenceClass) {
				mState2EquivalenceClass.put(state, equivalenceClass);
			}
		}
		generateVariables(transitivityGenerator);
		generateTransitionConstraints();
		if (!useTransitivityGenerator) {
			generateTransitivityConstraints();
		}
		mLogger.info(
				"Number of clauses for: -> acceptance: "
						+ mNumberClauses_Acceptance
						+ ", -> transitions: "
						+ mNumberClauses_Transitions
						+ ", -> nondeterministic transitions: "
						+ mNumberClauses_Transitions_Nondeterministic
						+ ", -> transitivity: "
						+ mNumberClauses_Transitivity);
		final boolean satisfiable = mSolver.solve();
		if (!satisfiable) {
			throw new AssertionError("Constructed constraints were unsatisfiable");
		}
		final UnionFind<STATE> resultingEquivalenceClasses =
				constructEquivalenceClasses();
		constructResultFromUnionFind(resultingEquivalenceClasses, addMapOldState2newState);
	}
	
	@SuppressWarnings("squid:S1698")
	private boolean haveSimilarEquivalenceClass(final STATE inputState1, final STATE inputState2) {
		return mState2EquivalenceClass.get(inputState1) == mState2EquivalenceClass.get(inputState2);
	}
	
	private STATE[] constructStateArray(final Collection<STATE> states) {
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
				final STATE rep1 = resultingEquivalenceClasses
						.findAndConstructEquivalenceClassIfNeeded(entry.getKey().getOneElement());
				final STATE rep2 = resultingEquivalenceClasses
						.findAndConstructEquivalenceClassIfNeeded(entry.getKey().getOtherElement());
				resultingEquivalenceClasses.union(rep1, rep2);
			} else {
				// do nothing
			}
		}
		return resultingEquivalenceClasses;
	}
	
	private void generateVariables(final ScopedTransitivityGenerator<STATE> transitivityGenerator)
			throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i = 0; i < states.length; i++) {
				// add to transitivity generator
				if ((transitivityGenerator != null) && (states.length > 1)) {
					transitivityGenerator.addContent(states[i]);
				}
				
				for (int j = 0; j < i; j++) {
					final Doubleton<STATE> doubleton = new Doubleton<STATE>(states[i], states[j]);
					mStatePairs.put(states[i], states[j], doubleton);
					mStatePairs.put(states[j], states[i], doubleton);
					mSolver.addVariable(doubleton);
					if (mUseFinalStateConstraints
							&& (mOperand.isFinal(states[i]) ^ mOperand.isFinal(states[j]))) {
						setStatesDifferent(doubleton);
						mNumberClauses_Acceptance++;
					}
				}
			}
			checkTimeout();
		}
	}
	
	/**
	 * Tells the solver that two states are different.
	 */
	private void setStatesDifferent(final Doubleton<STATE> doubleton) {
		mSolver.addHornClause(consArr(doubleton), null);
	}
	
	/**
	 * Tells the solver that two states are different.
	 */
	private void setStatesDifferent(final STATE state1, final STATE state2) {
		setStatesDifferent(mStatePairs.get(state1, state2));
	}
	
	private void generateTransitionConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i = 0; i < states.length; i++) {
				final STATE state1 = states[i];
				final STATE[] downStates1 = constructStateArray(mOperand.getDownStates(state1));
				for (int j = 0; j < i; j++) {
					final STATE state2 = states[j];
					final boolean predPairKnowToBeSimilar;
					if (i != j) {
						// this condition is for efficiency reasons only
						
						if (knownToBeDifferent(state1, state2)) {
							// all corresponding clauses are trivially true
							continue;
						}
						
						if (!haveSameOutgoingInternalCallSymbols(state1, state2)) {
							// not known to be different, report to the solver
							setStatesDifferent(state1, state2);
							
							// all corresponding clauses are trivially true
							continue;
						}
						
						predPairKnowToBeSimilar = knownToBeSimilar(state1, state2);
					} else {
						predPairKnowToBeSimilar = true;
					}
					
					final Doubleton<STATE> predDoubleton =
							getDoubleton(state1, state2, predPairKnowToBeSimilar);
					
					if (mUseTransitionHornClauses) {
						generateTransitionConstraint_Internal_Horn(
								state1, state2, predDoubleton);
						generateTransitionConstraint_Call_Horn(
								state1, state2, predDoubleton);
					} else {
						generateTransitionConstraint_Internal_General(
								state1, state2, predDoubleton);
						generateTransitionConstraint_Call_General(
								state1, state2, predDoubleton);
					}
					
					// NOTE: slower iteration outside
					for (final STATE down2 : mOperand.getDownStates(state2)) {
						for (final STATE down1 : downStates1) {
							if (mUseTransitionHornClauses) {
								generateTransitionConstraint_Return_Horn(
										state1, state2, predDoubleton, down1, down2);
							} else {
								generateTransitionConstraint_Return_General(
										state1, state2, predDoubleton, down1, down2);
							}
						}
					}
				}
				for (int k = 0; k < downStates1.length; k++) {
					for (int l = 0; l < k; l++) {
						if (mUseTransitionHornClauses) {
							generateTransitionConstraint_Return_Horn(
									state1, state1, null, downStates1[k], downStates1[l]);
						} else {
							generateTransitionConstraint_Return_General(
									state1, state1, null, downStates1[k], downStates1[l]);
						}
					}
				}
				checkTimeout();
			}
		}
	}
	
	private void generateTransitionConstraint_Internal_Horn(
			final STATE predState1, final STATE predState2,
			final Doubleton<STATE> predDoubleton) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans1 : mOperand.internalSuccessors(predState1)) {
			final STATE succState1 = trans1.getSucc();
			for (final OutgoingInternalTransition<LETTER, STATE> trans2 : mOperand.internalSuccessors(predState2,
					trans1.getLetter())) {
				final STATE succState2 = trans2.getSucc();
				generateBinaryTransitionConstraint(predDoubleton, succState1, succState2);
			}
		}
	}
	
	private void generateTransitionConstraint_Internal_General(
			final STATE predState1, final STATE predState2,
			final Doubleton<STATE> predDoubleton) {
		outer: for (final OutgoingInternalTransition<LETTER, STATE> trans1 : mOperand.internalSuccessors(predState1)) {
			final STATE succState1 = trans1.getSucc();
			final List<STATE> succStates2 = new ArrayList<>();
			for (final OutgoingInternalTransition<LETTER, STATE> trans2 : mOperand.internalSuccessors(predState2,
					trans1.getLetter())) {
				final STATE succState2 = trans2.getSucc();
				if (knownToBeSimilar(succState1, succState2)) {
					// clause is trivially true, continue with next state
					continue outer;
				}
				succStates2.add(succState2);
			}
			generateNaryTransitionConstraint(predDoubleton, succState1, succStates2);
		}
	}
	
	private void generateTransitionConstraint_Call_Horn(
			final STATE predState1, final STATE predState2,
			final Doubleton<STATE> predDoubleton) {
		for (final OutgoingCallTransition<LETTER, STATE> trans1 : mOperand.callSuccessors(predState1)) {
			final STATE succState1 = trans1.getSucc();
			for (final OutgoingCallTransition<LETTER, STATE> trans2 : mOperand.callSuccessors(predState2,
					trans1.getLetter())) {
				final STATE succState2 = trans2.getSucc();
				generateBinaryTransitionConstraint(predDoubleton, succState1, succState2);
			}
		}
	}
	
	private void generateTransitionConstraint_Call_General(
			final STATE predState1, final STATE predState2,
			final Doubleton<STATE> predDoubleton) {
		outer: for (final OutgoingCallTransition<LETTER, STATE> trans1 : mOperand.callSuccessors(predState1)) {
			final STATE succState1 = trans1.getSucc();
			final List<STATE> succStates2 = new ArrayList<>();
			for (final OutgoingCallTransition<LETTER, STATE> trans2 : mOperand.callSuccessors(predState2,
					trans1.getLetter())) {
				final STATE succState2 = trans2.getSucc();
				if (knownToBeSimilar(succState1, succState2)) {
					// clause is trivially true, continue with next state
					continue outer;
				}
				succStates2.add(succState2);
			}
			generateNaryTransitionConstraint(predDoubleton, succState1, succStates2);
		}
	}
	
	private void generateTransitionConstraint_Return_Horn(
			final STATE linPredState1, final STATE linPredState2,
			final Doubleton<STATE> linPredDoubleton,
			final STATE hierPredState1, final STATE hierPredState2) {
		if (knownToBeDifferent(hierPredState1, hierPredState2)) {
			// all corresponding clauses are trivially true
			return;
		}
		
		final Doubleton<STATE> hierPredDoubleton =
				getDoubletonIfNotSimilar(hierPredState1, hierPredState2);
		if (!haveSameOutgoingReturnSymbols(linPredState1, hierPredState1,
				linPredState2, hierPredState2)) {
			addThreeLiteralHornClause(linPredDoubleton, hierPredDoubleton, null);
		} else {
			// both DoubleDeckers have same outgoing return symbols
			outer: for (final OutgoingReturnTransition<LETTER, STATE> trans1 : mOperand
					.returnSuccessorsGivenHier(linPredState1, hierPredState1)) {
				for (final OutgoingReturnTransition<LETTER, STATE> trans2 : mOperand.returnSuccessors(linPredState2,
						hierPredState2,
						trans1.getLetter())) {
					if (knownToBeSimilar(trans1.getSucc(), trans2.getSucc())) {
						// clause is trivially true, continue with next state
						continue outer;
					}
					final Doubleton<STATE> succDoubleton =
							getDoubletonIfNotDifferent(trans1.getSucc(), trans2.getSucc());
					addThreeLiteralHornClause(linPredDoubleton, hierPredDoubleton, succDoubleton);
				}
			}
		}
	}
	
	private void generateTransitionConstraint_Return_General(
			final STATE linPredState1, final STATE linPredState2,
			final Doubleton<STATE> linPredDoubleton,
			final STATE hierPredState1, final STATE hierPredState2) {
		if (knownToBeDifferent(hierPredState1, hierPredState2)) {
			// all corresponding clauses are trivially true
			return;
		}
		
		final Doubleton<STATE> hierPredDoubleton =
				getDoubletonIfNotSimilar(hierPredState1, hierPredState2);
		if (!haveSameOutgoingReturnSymbols(linPredState1, hierPredState1, linPredState2, hierPredState2)) {
			addThreeLiteralHornClause(linPredDoubleton, hierPredDoubleton, null);
		} else {
			// both DoubleDeckers have same outgoing return symbols
			outer: for (final OutgoingReturnTransition<LETTER, STATE> trans1 : mOperand
					.returnSuccessorsGivenHier(linPredState1, hierPredState1)) {
				final STATE succState1 = trans1.getSucc();
				final List<STATE> succStates2 = new ArrayList<>();
				for (final OutgoingReturnTransition<LETTER, STATE> trans2 : mOperand.returnSuccessors(linPredState2,
						hierPredState2,
						trans1.getLetter())) {
					final STATE succState2 = trans2.getSucc();
					if (knownToBeSimilar(succState1, succState2)) {
						// clause is trivially true, continue with next state
						continue outer;
					}
					succStates2.add(succState2);
				}
				generateNaryTransitionConstraint(linPredDoubleton,
						hierPredDoubleton, succState1, succStates2);
			}
		}
	}
	
	private Doubleton<STATE> getDoubletonIfNotDifferent(
			final STATE state1, final STATE state2) {
		return getDoubleton(state1, state2, knownToBeDifferent(state1, state2));
	}
	
	private Doubleton<STATE> getDoubletonIfNotSimilar(
			final STATE state1, final STATE state2) {
		return getDoubleton(state1, state2, knownToBeSimilar(state1, state2));
	}
	
	/**
	 * @param state1
	 *            state 1
	 * @param state2
	 *            state 2
	 * @param flag
	 *            true iff null should be returned
	 * @return doubleton of two states iff the flag is not true, null otherwise
	 */
	private Doubleton<STATE> getDoubleton(
			final STATE state1, final STATE state2, final boolean flag) {
		final Doubleton<STATE> doubleton;
		if (flag) {
			doubleton = null;
		} else {
			doubleton = mStatePairs.get(state1, state2);
		}
		return doubleton;
	}
	
	private void generateBinaryTransitionConstraint(
			final Doubleton<STATE> predDoubleton,
			final STATE succState1, final STATE succState2) {
		// first check whether the clause is trivially true
		if (knownToBeSimilar(succState1, succState2)) {
			return;
		}
		
		final Doubleton<STATE> succDoubleton =
				getDoubletonIfNotDifferent(succState1, succState2);
		addTwoLiteralHornClause(predDoubleton, succDoubleton);
	}
	
	@SuppressWarnings("unchecked")
	private void generateNaryTransitionConstraint(
			final Doubleton<STATE> predDoubleton,
			final STATE succState1, final List<STATE> succStates2) {
		final List<Doubleton<STATE>> succDoubletons = new ArrayList<>();
		for (final STATE succState2 : succStates2) {
			if (!knownToBeDifferent(succState1, succState2)) {
				final Doubleton<STATE> succDoubleton =
						mStatePairs.get(succState1, succState2);
				succDoubletons.add(succDoubleton);
			}
		}
		final Doubleton<STATE>[] negativeAtoms =
				(predDoubleton == null)
						? (new Doubleton[0])
						: (new Doubleton[] { predDoubleton });
		final Doubleton<STATE>[] positiveAtoms = consArr(succDoubletons);
		addArbitraryLiteralClause(negativeAtoms, positiveAtoms);
	}
	
	@SuppressWarnings("unchecked")
	private void generateNaryTransitionConstraint(
			final Doubleton<STATE> linPredDoubleton,
			final Doubleton<STATE> hierPredDoubleton, final STATE succState1,
			final List<STATE> succStates2) {
		final List<Doubleton<STATE>> succDoubletons = new ArrayList<>();
		for (final STATE succState2 : succStates2) {
			if (!knownToBeDifferent(succState1, succState2)) {
				final Doubleton<STATE> succDoubleton =
						mStatePairs.get(succState1, succState2);
				succDoubletons.add(succDoubleton);
			}
		}
		
		final Doubleton<STATE>[] negativeAtoms;
		if (linPredDoubleton == null) {
			if (hierPredDoubleton == null) {
				negativeAtoms = new Doubleton[0];
			} else {
				negativeAtoms = new Doubleton[] { hierPredDoubleton };
			}
		} else {
			if (hierPredDoubleton == null) {
				negativeAtoms = new Doubleton[] { linPredDoubleton };
			} else {
				negativeAtoms = new Doubleton[] { linPredDoubleton, hierPredDoubleton };
			}
		}
		final Doubleton<STATE>[] positiveAtoms = consArr(succDoubletons);
		addArbitraryLiteralClause(negativeAtoms, positiveAtoms);
	}
	
	private void addArbitraryLiteralClause(
			final Doubleton<STATE>[] negativeAtoms,
			final Doubleton<STATE>[] positiveAtoms) {
		assert voidOfNull(negativeAtoms) && voidOfNull(positiveAtoms) : "Array/list must be void of null elements.";
		assert (negativeAtoms.length == 1) || (negativeAtoms.length == 2) : "Always pass one or two negative atoms.";
		if (positiveAtoms.length <= 1) {
			// deterministic case
			final Doubleton<STATE> positiveAtom = (positiveAtoms.length == 1)
					? positiveAtoms[0]
					: null;
			if (negativeAtoms.length == 1) {
				addTwoLiteralHornClause(negativeAtoms[0], positiveAtom);
			} else {
				addThreeLiteralHornClause(negativeAtoms[0], negativeAtoms[1],
						positiveAtom);
			}
		} else {
			// nondeterministic case
			mSolver.addClause(negativeAtoms, positiveAtoms);
			mNumberClauses_Transitions_Nondeterministic++;
		}
	}
	
	@SuppressWarnings("unchecked")
	private void addTwoLiteralHornClause(final Doubleton<STATE> negativeAtom, final Doubleton<STATE> positiveAtom) {
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
	
	@SuppressWarnings("unchecked")
	private void addThreeLiteralHornClause(final Doubleton<STATE> negativeAtom1, final Doubleton<STATE> negativeAtom2,
			final Doubleton<STATE> positiveAtom) {
		if (negativeAtom1 == null) {
			addTwoLiteralHornClause(negativeAtom2, positiveAtom);
		} else if (negativeAtom2 == null) {
			addTwoLiteralHornClause(negativeAtom1, positiveAtom);
		} else {
			mSolver.addHornClause(consArr(negativeAtom1, negativeAtom2), positiveAtom);
			mNumberClauses_Transitions++;
		}
	}
	
	/**
	 * @return true iff two states have the same outgoing internal and call symbols
	 */
	private boolean haveSameOutgoingInternalCallSymbols(final STATE predState1,
			final STATE predState2) {
		// internal symbols
		Set<LETTER> letters1 = mOperand.lettersInternal(predState1);
		Set<LETTER> letters2 = mOperand.lettersInternal(predState2);
		if (!letters1.equals(letters2)) {
			return false;
		}
		
		// call symbols
		letters1 = mOperand.lettersCall(predState1);
		letters2 = mOperand.lettersCall(predState2);
		if (!letters1.equals(letters2)) {
			return false;
		}
		
		return true;
	}
	
	/**
	 * @return true iff two states have the same outgoing return symbols wrt.
	 *         hierarchical predecessors
	 */
	private boolean haveSameOutgoingReturnSymbols(final STATE up1, final STATE down1, final STATE up2,
			final STATE down2) {
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
	
	private VariableStatus resultFromSolver(final STATE inputState1,
			final STATE inputState2) {
		assert haveSimilarEquivalenceClass(inputState1, inputState2) : "check not available";
		final Doubleton<STATE> doubleton =
				mStatePairs.get(inputState1, inputState2);
		return mSolver.getValue(doubleton);
	}
	
	private boolean solverSaysDifferent(final STATE inputState1, final STATE inputState2) {
		return resultFromSolver(inputState1, inputState2) == VariableStatus.FALSE;
	}
	
	private boolean solverSaysSimilar(final STATE inputState1, final STATE inputState2) {
		return resultFromSolver(inputState1, inputState2) == VariableStatus.TRUE;
	}
	
	private boolean knownToBeSimilar(final STATE inputState1, final STATE inputState2) {
		if (inputState1.equals(inputState2)) {
			return true;
		} else {
			if (haveSimilarEquivalenceClass(inputState1, inputState2)) {
				return solverSaysSimilar(inputState1, inputState2);
			} else {
				return false;
			}
		}
	}
	
	private boolean knownToBeDifferent(final STATE inputState1, final STATE inputState2) {
		if (haveSimilarEquivalenceClass(inputState1, inputState2)) {
			return solverSaysDifferent(inputState1, inputState2);
		} else {
			return true;
		}
	}
	
	private void generateTransitivityConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i = 0; i < states.length; i++) {
				for (int j = 0; j < i; j++) {
					// TODO: use already computed solver information to save
					// some time
					// will not safe much, because solver does this quickly
					for (int k = 0; k < j; k++) {
						final Doubleton<STATE> doubleton_ij = mStatePairs.get(states[i], states[j]);
						final Doubleton<STATE> doubleton_jk = mStatePairs.get(states[j], states[k]);
						final Doubleton<STATE> doubleton_ik = mStatePairs.get(states[i], states[k]);
						mSolver.addHornClause(consArr(doubleton_ij, doubleton_jk), doubleton_ik);
						mSolver.addHornClause(consArr(doubleton_jk, doubleton_ik), doubleton_ij);
						mSolver.addHornClause(consArr(doubleton_ik, doubleton_ij), doubleton_jk);
						mNumberClauses_Transitivity += 3;
					}
					checkTimeout();
				}
			}
		}
	}
	
	private Doubleton<STATE>[] consArr(final Doubleton<STATE>... doubletons) {
		return doubletons;
	}
	
	@SuppressWarnings("unchecked")
	private Doubleton<STATE>[] consArr(final Collection<Doubleton<STATE>> doubletons) {
		return doubletons.toArray(new Doubleton[doubletons.size()]);
	}
	
	private <T> boolean voidOfNull(final T[] positiveAtoms) {
		for (final T elem : positiveAtoms) {
			if (elem == null) {
				return false;
			}
		}
		return true;
	}
	
	private void checkTimeout() throws AutomataOperationCanceledException {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}
	}
}
