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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.GeneralMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.HornMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.TransitivityGeneralMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.VariableStatus;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaMaxSat2<LETTER, STATE> extends AbstractMinimizeNwaDd<LETTER, STATE> {
	private static final int THREE = 3;
	
	private final NestedMap2<STATE, STATE, Doubleton<STATE>> mStatePairs = new NestedMap2<>();
	private final AbstractMaxSatSolver<Doubleton<STATE>> mSolver;
	private final Collection<Set<STATE>> mInitialEquivalenceClasses;
	private final Map<STATE, Set<STATE>> mState2EquivalenceClass;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final boolean mUseFinalStateConstraints;
	
	// if true, we can omit transitivity clauses
	private final boolean mOperandHasNoReturns;
	
	private int mNumberClausesAcceptance;
	private int mNumberClausesTransitions;
	private int mNumberClausesTransitionsNondeterministic;
	private int mNumberClausesTransitivity;
	/**
	 * This flag can also be set for nondeterministic automata.
	 * However, the results might not be satisfactory: all successors have to be
	 * be similar in this case.
	 */
	private final boolean mUseTransitionHornClauses;

	private final int mLargestBlockInitialPartition;
	
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
	public MinimizeNwaMaxSat2(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, true, new LookaheadPartitionConstructor<>(services, operand).getResult());
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
	public MinimizeNwaMaxSat2(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final boolean addMapOldState2newState,
			final Collection<Set<STATE>> initialEquivalenceClasses) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, addMapOldState2newState, initialEquivalenceClasses, true, false, false,
				true, false);
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
	 * @param initialPartition
	 *            We only try to merge states that are in one of the blocks.
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
	public MinimizeNwaMaxSat2(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final boolean addMapOldState2newState,
			final Collection<Set<STATE>> initialPartition, final boolean useFinalStateConstraints,
			final boolean useTransitionHornClauses, final boolean useHornSolver, final boolean useTransitivityGenerator,
			final boolean usePathCompression) throws AutomataOperationCanceledException {
		super(services, stateFactory, "minimizeNwaMaxSat2", operand);
		mOperand = operand;
		// if (!new IsDeterministic<>(mServices, operand).getResult()) {
		// throw new AssertionError("not deterministic");
		// }
		mUseFinalStateConstraints = useFinalStateConstraints;
		mInitialEquivalenceClasses = initialPartition;
		mUseTransitionHornClauses = useTransitionHornClauses;
		mOperandHasNoReturns = mOperand.getReturnAlphabet().isEmpty();
		
		// TODO even copy an existing HashMap?
		mState2EquivalenceClass = new HashMap<>();
		int largestBlockInitialPartition = 0;
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			for (final STATE state : equivalenceClass) {
				mState2EquivalenceClass.put(state, equivalenceClass);
			}
			largestBlockInitialPartition = Math.max(largestBlockInitialPartition, equivalenceClass.size());
		}
		mLargestBlockInitialPartition = largestBlockInitialPartition;
		
		// create solver
		if (!mUseTransitionHornClauses && useHornSolver) {
			throw new IllegalArgumentException(
					"For using the Horn solver you must use Horn clauses.");
		}
		ScopedTransitivityGenerator<STATE> transitivityGenerator = null;
		if (useHornSolver) {
			mSolver = new HornMaxSatSolver<>(mServices);
		} else {
			if (useTransitivityGenerator && !mOperandHasNoReturns) {
				transitivityGenerator = new ScopedTransitivityGenerator<>(usePathCompression);
				mSolver = new TransitivityGeneralMaxSatSolver<>(mServices, transitivityGenerator);
			} else {
				mSolver = new GeneralMaxSatSolver<>(mServices);
			}
		}
		
		feedSolver(useTransitivityGenerator, transitivityGenerator);
		
		constructResult(addMapOldState2newState);
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}
	
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = super.getAutomataOperationStatistics();
		if (mLargestBlockInitialPartition != 0) {
			statistics.addKeyValuePair(StatisticsType.SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS,
					mLargestBlockInitialPartition);
		}
		return statistics;
	}
	
	private void constructResult(final boolean addMapOldState2newState)
			throws AutomataOperationCanceledException, AssertionError {
		final boolean satisfiable = mSolver.solve();
		if (!satisfiable) {
			throw new AssertionError("Constructed constraints were unsatisfiable");
		}
		final UnionFind<STATE> resultingEquivalenceClasses =
				constructEquivalenceClasses();
		constructResultFromUnionFind(resultingEquivalenceClasses, addMapOldState2newState);
	}
	
	private void feedSolver(final boolean useTransitivityGenerator,
			final ScopedTransitivityGenerator<STATE> transitivityGenerator) throws AutomataOperationCanceledException {
		generateVariables(transitivityGenerator);
		generateTransitionConstraints();
		if (!useTransitivityGenerator && !mOperandHasNoReturns) {
			generateTransitivityConstraints();
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info(
					"Number of clauses for: -> acceptance: " + mNumberClausesAcceptance + ", -> transitions: "
							+ mNumberClausesTransitions + ", -> nondeterministic transitions: "
							+ mNumberClausesTransitionsNondeterministic + ", -> transitivity: "
							+ mNumberClausesTransitivity);
		}
	}
	
	@Override
	protected Pair<Boolean, String> checkResultHelper(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// check language equivalence
		final Pair<Boolean, String> result1 = checkLanguageEquivalence(stateFactory);
		if (!result1.getFirst()) {
			return result1;
		}
		
//		if (mOperandHasNoReturns) {
//			// check that direct simulation is the same for automata without calls and returns
//			// TODO use new direct simulation when it also supports an initial partition
//			final ReduceNwaDirectSimulation<LETTER, STATE> directSimulation = new ReduceNwaDirectSimulation<>(mServices,
//					stateFactory, mOperand, false, mInitialEquivalenceClasses);
//			final int directSimulationSize = directSimulation.getResult().size();
//			final int resultSize = getResult().size();
//			if (resultSize != directSimulationSize) {
//				return new Pair<>(Boolean.FALSE,
//						String.format("The result has %d states, but the direct simulation result has %d states.",
//								resultSize, directSimulationSize));
//			}
//		}
		
		return new Pair<>(Boolean.TRUE, "");
	}
	
	@SuppressWarnings("squid:S1698")
	private boolean haveSimilarEquivalenceClass(final STATE inputState1, final STATE inputState2) {
		// equality intended here
		return mState2EquivalenceClass.get(inputState1) == mState2EquivalenceClass.get(inputState2);
	}
	
	@SuppressWarnings("unchecked")
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
			generateVariablesHelper(transitivityGenerator, states);
			checkTimeout();
		}
	}
	
	private void generateVariablesHelper(final ScopedTransitivityGenerator<STATE> transitivityGenerator,
			final STATE[] states) {
		for (int i = 0; i < states.length; i++) {
			// add to transitivity generator
			if ((transitivityGenerator != null) && (states.length > 1)) {
				transitivityGenerator.addContent(states[i]);
			}
			
			for (int j = 0; j < i; j++) {
				final Doubleton<STATE> doubleton = new Doubleton<>(states[i], states[j]);
				mStatePairs.put(states[i], states[j], doubleton);
				mStatePairs.put(states[j], states[i], doubleton);
				mSolver.addVariable(doubleton);
				if (mUseFinalStateConstraints && (mOperand.isFinal(states[i]) ^ mOperand.isFinal(states[j]))) {
					setStatesDifferent(doubleton);
					mNumberClausesAcceptance++;
				}
			}
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
				generateTransitionConstraintsHelper(states, i);
				checkTimeout();
			}
		}
	}
	
	private void generateTransitionConstraintsHelper(final STATE[] states, final int firstStateIndex) {
		final STATE state1 = states[firstStateIndex];
		final STATE[] downStates1 = constructStateArray(mOperand.getDownStates(state1));
		for (int j = 0; j < firstStateIndex; j++) {
			final STATE state2 = states[j];
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
			
			final boolean predPairKnowToBeSimilar = knownToBeSimilar(state1, state2);
			
			final Doubleton<STATE> predDoubleton = getDoubleton(state1, state2, predPairKnowToBeSimilar);
			
			if (mUseTransitionHornClauses) {
				generateTransitionConstraintInternalHorn(state1, state2, predDoubleton);
				generateTransitionConstraintCallHorn(state1, state2, predDoubleton);
			} else {
				generateTransitionConstraintInternalGeneral(state1, state2, predDoubleton);
				generateTransitionConstraintCallGeneral(state1, state2, predDoubleton);
			}
			
			generateTransitionConstraintsHelperReturn1(state1, downStates1, state2, predDoubleton);
		}
		generateTransitionConstraintsHelperReturn2(state1, downStates1);
	}
	
	private void generateTransitionConstraintsHelperReturn1(final STATE state1, final STATE[] downStates1,
			final STATE state2, final Doubleton<STATE> predDoubleton) {
		// NOTE: slower iteration outside
		for (final STATE down2 : mOperand.getDownStates(state2)) {
			for (final STATE down1 : downStates1) {
				if (mUseTransitionHornClauses) {
					generateTransitionConstraintReturnHorn(state1, state2, predDoubleton, down1, down2);
				} else {
					generateTransitionConstraintReturnGeneral(state1, state2, predDoubleton, down1, down2);
				}
			}
		}
	}
	
	private void generateTransitionConstraintsHelperReturn2(final STATE state1, final STATE[] downStates1) {
		for (int k = 0; k < downStates1.length; k++) {
			for (int l = 0; l < k; l++) {
				if (mUseTransitionHornClauses) {
					generateTransitionConstraintReturnHorn(state1, state1, null, downStates1[k], downStates1[l]);
				} else {
					generateTransitionConstraintReturnGeneral(state1, state1, null, downStates1[k], downStates1[l]);
				}
			}
		}
	}
	
	private void generateTransitionConstraintInternalHorn(
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
	
	private void generateTransitionConstraintInternalGeneral(final STATE predState1, final STATE predState2,
			final Doubleton<STATE> predDoubleton) {
		// NOTE: We exploit the knowledge that the states have the same outgoing symbols
		for (final LETTER letter : mOperand.lettersInternal(predState1)) {
			final Set<STATE> succs1 = new LinkedHashSet<>();
			final Set<STATE> succs2 = new LinkedHashSet<>();
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(predState1,
					letter)) {
				succs1.add(trans.getSucc());
			}
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(predState2,
					letter)) {
				succs2.add(trans.getSucc());
			}
			generateTransitionConstraintGeneralInternalCallHelperSymmetric(predDoubleton, succs1, succs2);
		}
	}
	
	private void generateTransitionConstraintCallHorn(final STATE predState1, final STATE predState2,
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
	
	private void generateTransitionConstraintCallGeneral(final STATE predState1, final STATE predState2,
			final Doubleton<STATE> predDoubleton) {
		// NOTE: We exploit the knowledge that the states have the same outgoing symbols
		for (final LETTER letter : mOperand.lettersCall(predState1)) {
			final Set<STATE> succs1 = new LinkedHashSet<>();
			final Set<STATE> succs2 = new LinkedHashSet<>();
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(predState1,
					letter)) {
				succs1.add(trans.getSucc());
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(predState2,
					letter)) {
				succs2.add(trans.getSucc());
			}
			generateTransitionConstraintGeneralInternalCallHelperSymmetric(predDoubleton, succs1, succs2);
		}
	}
	
	private void generateTransitionConstraintGeneralInternalCallHelperSymmetric(final Doubleton<STATE> predDoubleton,
			final Set<STATE> succs1, final Set<STATE> succs2) {
		final Collection<STATE> succsToRemove = new ArrayList<>();
		
		generateTransitionConstraintGeneralInternalCallHelperOneSide(predDoubleton, succs1, succs2, succsToRemove);
		/*
		 * Optimization: If a state from the second set is known to be similar to another on from the first set, we
		 * should not try to add a clause for the other direction (as it will be found out again that they are
		 * similar).
		 */
		succs2.removeAll(succsToRemove);
		
		generateTransitionConstraintGeneralInternalCallHelperOneSide(predDoubleton, succs2, succs1, null);
	}
	
	private void generateTransitionConstraintGeneralInternalCallHelperOneSide(final Doubleton<STATE> predDoubleton,
			final Iterable<STATE> succs1, final Iterable<STATE> succs2, final Collection<STATE> succsToRemove) {
		boolean ignoreConstraint = false;
		for (final STATE succState1 : succs1) {
			for (final STATE succState2 : succs2) {
				if (knownToBeSimilar(succState1, succState2)) {
					// clause is trivially true
					
					// remember this state, it needs not be checked in the other direction
					addIfNotNull(succsToRemove, succState2);
					
					// continue with next state
					ignoreConstraint = true;
					break;
				}
			}
			if (ignoreConstraint) {
				ignoreConstraint = false;
			} else {
				// create new transition clause
				generateNaryTransitionConstraint(predDoubleton, succState1, succs2);
			}
		}
	}
	
	private void addIfNotNull(final Collection<STATE> collection, final STATE element) {
		if (collection != null) {
			collection.add(element);
		}
	}
	
	private void generateTransitionConstraintReturnHorn(final STATE linPredState1, final STATE linPredState2,
			final Doubleton<STATE> linPredDoubleton, final STATE hierPredState1, final STATE hierPredState2) {
		if (knownToBeDifferent(hierPredState1, hierPredState2)) {
			// all corresponding clauses are trivially true
			return;
		}
		
		final Doubleton<STATE> hierPredDoubleton = getDoubletonIfNotSimilar(hierPredState1, hierPredState2);
		if (!haveSameOutgoingReturnSymbols(linPredState1, hierPredState1, linPredState2, hierPredState2)) {
			addThreeLiteralHornClause(linPredDoubleton, hierPredDoubleton, null);
			return;
		}
		// both DoubleDeckers have same outgoing return symbols
		for (final OutgoingReturnTransition<LETTER, STATE> trans1 : mOperand
				.returnSuccessorsGivenHier(linPredState1, hierPredState1)) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans2 : mOperand.returnSuccessors(linPredState2,
					hierPredState2, trans1.getLetter())) {
				if (knownToBeSimilar(trans1.getSucc(), trans2.getSucc())) {
					// clause is trivially true, continue with next state
					break;
				}
				final Doubleton<STATE> succDoubleton =
						getDoubletonIfNotDifferent(trans1.getSucc(), trans2.getSucc());
				addThreeLiteralHornClause(linPredDoubleton, hierPredDoubleton, succDoubleton);
			}
		}
	}
	
	private void generateTransitionConstraintReturnGeneral(final STATE linPredState1, final STATE linPredState2,
			final Doubleton<STATE> linPredDoubleton, final STATE hierPredState1, final STATE hierPredState2) {
		if (knownToBeDifferent(hierPredState1, hierPredState2)) {
			// all corresponding clauses are trivially true
			return;
		}
		
		final Doubleton<STATE> hierPredDoubleton = getDoubletonIfNotSimilar(hierPredState1, hierPredState2);
		final Set<LETTER> sameOutgoingReturnSymbols =
				getSameOutgoingReturnSymbols(linPredState1, hierPredState1, linPredState2, hierPredState2);
		if (sameOutgoingReturnSymbols == null) {
			addThreeLiteralHornClause(linPredDoubleton, hierPredDoubleton, null);
		} else {
			// both DoubleDeckers have same outgoing return symbols
			
			// NOTE: We exploit the knowledge that the states have the same outgoing symbols
			for (final LETTER letter : sameOutgoingReturnSymbols) {
				final Set<STATE> succs1 = new LinkedHashSet<>();
				final Set<STATE> succs2 = new LinkedHashSet<>();
				for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(linPredState1,
						hierPredState1, letter)) {
					succs1.add(trans.getSucc());
				}
				for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(linPredState2,
						hierPredState2, letter)) {
					succs2.add(trans.getSucc());
				}
				generateTransitionConstraintGeneralReturnHelperSymmetric(linPredDoubleton, hierPredDoubleton,
						succs1, succs2);
			}
		}
	}
	
	private void generateTransitionConstraintGeneralReturnHelperSymmetric(final Doubleton<STATE> linPredDoubleton,
			final Doubleton<STATE> hierPredDoubleton, final Set<STATE> succs1, final Set<STATE> succs2) {
		final Collection<STATE> succsToRemove = new ArrayList<>();
		
		generateTransitionConstraintGeneralReturnHelperOneSide(linPredDoubleton, hierPredDoubleton, succs1, succs2,
				succsToRemove);
		/*
		 * Optimization: If a state from the second set is known to be similar to another on from the first set, we
		 * should not try to add a clause for the other direction (as it will be found out again that they are
		 * similar).
		 */
		succs2.removeAll(succsToRemove);
		
		generateTransitionConstraintGeneralReturnHelperOneSide(linPredDoubleton, hierPredDoubleton, succs2, succs1,
				null);
	}
	
	private void generateTransitionConstraintGeneralReturnHelperOneSide(final Doubleton<STATE> linPredDoubleton,
			final Doubleton<STATE> hierPredDoubleton, final Set<STATE> succs1, final Set<STATE> succs2,
			final Collection<STATE> succsToRemove) {
		boolean ignore = false;
		for (final STATE succState1 : succs1) {
			for (final STATE succState2 : succs2) {
				if (knownToBeSimilar(succState1, succState2)) {
					// clause is trivially true
					
					addIfNotNull(succsToRemove, succState2);
					
					// continue with next state
					ignore = true;
					break;
				}
			}
			if (ignore) {
				ignore = false;
			} else {
				// create new transition clause
				generateNaryTransitionConstraint(linPredDoubleton, hierPredDoubleton, succState1, succs2);
			}
		}
	}
	
	private Doubleton<STATE> getDoubletonIfNotDifferent(final STATE state1, final STATE state2) {
		return getDoubleton(state1, state2, knownToBeDifferent(state1, state2));
	}
	
	private Doubleton<STATE> getDoubletonIfNotSimilar(final STATE state1, final STATE state2) {
		return getDoubleton(state1, state2, knownToBeSimilar(state1, state2));
	}
	
	/**
	 * Getter for a {@link Doubleton}.
	 * 
	 * @param state1
	 *            state 1
	 * @param state2
	 *            state 2
	 * @param flag
	 *            true iff null should be returned
	 * @return doubleton of two states iff the flag is not true, null otherwise
	 */
	private Doubleton<STATE> getDoubleton(final STATE state1, final STATE state2, final boolean flag) {
		final Doubleton<STATE> doubleton;
		if (flag) {
			doubleton = null;
		} else {
			doubleton = mStatePairs.get(state1, state2);
		}
		return doubleton;
	}
	
	private void generateBinaryTransitionConstraint(final Doubleton<STATE> predDoubleton, final STATE succState1,
			final STATE succState2) {
		// first check whether the clause is trivially true
		if (knownToBeSimilar(succState1, succState2)) {
			return;
		}
		
		final Doubleton<STATE> succDoubleton = getDoubletonIfNotDifferent(succState1, succState2);
		addTwoLiteralHornClause(predDoubleton, succDoubleton);
	}
	
	@SuppressWarnings("unchecked")
	private void generateNaryTransitionConstraint(final Doubleton<STATE> predDoubleton, final STATE succState1,
			final Iterable<STATE> succStates2) {
		final List<Doubleton<STATE>> succDoubletons = new ArrayList<>();
		for (final STATE succState2 : succStates2) {
			if (!knownToBeDifferent(succState1, succState2)) {
				final Doubleton<STATE> succDoubleton = mStatePairs.get(succState1, succState2);
				succDoubletons.add(succDoubleton);
			}
		}
		final Doubleton<STATE>[] negativeAtoms =
				(predDoubleton == null) ? (new Doubleton[0]) : (new Doubleton[] { predDoubleton });
		final Doubleton<STATE>[] positiveAtoms = consArr(succDoubletons);
		addArbitraryLiteralClause(negativeAtoms, positiveAtoms);
	}
	
	@SuppressWarnings("unchecked")
	private void generateNaryTransitionConstraint(final Doubleton<STATE> linPredDoubleton,
			final Doubleton<STATE> hierPredDoubleton, final STATE succState1, final Iterable<STATE> succStates2) {
		final List<Doubleton<STATE>> succDoubletons = new ArrayList<>();
		for (final STATE succState2 : succStates2) {
			if (!knownToBeDifferent(succState1, succState2)) {
				final Doubleton<STATE> succDoubleton = mStatePairs.get(succState1, succState2);
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
	
	private void addArbitraryLiteralClause(final Doubleton<STATE>[] negativeAtoms,
			final Doubleton<STATE>[] positiveAtoms) {
		assert voidOfNull(negativeAtoms) && voidOfNull(positiveAtoms) : "Array/list must be void of null elements.";
		assert (negativeAtoms.length == 1) || (negativeAtoms.length == 2) : "Always pass one or two negative atoms.";
		if (positiveAtoms.length <= 1) {
			// deterministic case
			final Doubleton<STATE> positiveAtom = (positiveAtoms.length == 1) ? positiveAtoms[0] : null;
			if (negativeAtoms.length == 1) {
				addTwoLiteralHornClause(negativeAtoms[0], positiveAtom);
			} else {
				addThreeLiteralHornClause(negativeAtoms[0], negativeAtoms[1], positiveAtom);
			}
		} else {
			// nondeterministic case
			mSolver.addClause(negativeAtoms, positiveAtoms);
			mNumberClausesTransitionsNondeterministic++;
		}
	}
	
	@SuppressWarnings("unchecked")
	private void addTwoLiteralHornClause(final Doubleton<STATE> negativeAtom, final Doubleton<STATE> positiveAtom) {
		if (negativeAtom == null) {
			if (positiveAtom == null) {
				throw new AssertionError("clause must not be empty");
			}
			mSolver.addHornClause(new Doubleton[0], positiveAtom);
		} else {
			mSolver.addHornClause(consArr(negativeAtom), positiveAtom);
		}
		mNumberClausesTransitions++;
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
			mNumberClausesTransitions++;
		}
	}
	
	/**
	 * @return {@code true} iff two states have the same outgoing internal and call symbols.
	 */
	private boolean haveSameOutgoingInternalCallSymbols(final STATE predState1, final STATE predState2) {
		// internal symbols
		Set<LETTER> letters1 = mOperand.lettersInternal(predState1);
		Set<LETTER> letters2 = mOperand.lettersInternal(predState2);
		if (!letters1.equals(letters2)) {
			return false;
		}
		
		// call symbols
		letters1 = mOperand.lettersCall(predState1);
		letters2 = mOperand.lettersCall(predState2);
		return letters1.equals(letters2);
	}
	
	/**
	 * @return {@code true} iff two states have the same outgoing return symbols with respect to hierarchical
	 *         predecessors.
	 */
	private boolean haveSameOutgoingReturnSymbols(final STATE up1, final STATE down1, final STATE up2,
			final STATE down2) {
		return getSameOutgoingReturnSymbols(up1, down1, up2, down2) != null;
	}
	
	/**
	 * @return A set of letters iff the two states have the same outgoing return symbols with respect to the
	 *         hierarchical predecessors, {@code null} otherwise.
	 */
	private Set<LETTER> getSameOutgoingReturnSymbols(final STATE up1, final STATE down1, final STATE up2,
			final STATE down2) {
		final Set<LETTER> returnLetters1 = new HashSet<>();
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessorsGivenHier(up1, down1)) {
			returnLetters1.add(trans.getLetter());
		}
		final Set<LETTER> returnLetters2 = new HashSet<>();
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessorsGivenHier(up2, down2)) {
			returnLetters2.add(trans.getLetter());
		}
		return returnLetters1.equals(returnLetters2) ? returnLetters1 : null;
	}
	
	private VariableStatus resultFromSolver(final STATE inputState1, final STATE inputState2) {
		assert haveSimilarEquivalenceClass(inputState1, inputState2) : "check not available";
		final Doubleton<STATE> doubleton = mStatePairs.get(inputState1, inputState2);
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
		}
		if (haveSimilarEquivalenceClass(inputState1, inputState2)) {
			return solverSaysSimilar(inputState1, inputState2);
		}
		return false;
	}
	
	private boolean knownToBeDifferent(final STATE inputState1, final STATE inputState2) {
		if (haveSimilarEquivalenceClass(inputState1, inputState2)) {
			return solverSaysDifferent(inputState1, inputState2);
		}
		return true;
	}
	
	private void generateTransitivityConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialEquivalenceClasses) {
			final STATE[] states = constructStateArray(equivalenceClass);
			generateTransitivityConstraintsHelper(states);
		}
	}
	
	private void generateTransitivityConstraintsHelper(final STATE[] states) throws AutomataOperationCanceledException {
		for (int i = 0; i < states.length; i++) {
			for (int j = 0; j < i; j++) {
				/*
				 * TODO: use already computed solver information to save some time; will not safe much, because
				 * the solver does this quickly
				 */
				for (int k = 0; k < j; k++) {
					final Doubleton<STATE> doubletonIj = mStatePairs.get(states[i], states[j]);
					final Doubleton<STATE> doubletonJk = mStatePairs.get(states[j], states[k]);
					final Doubleton<STATE> doubletonIk = mStatePairs.get(states[i], states[k]);
					mSolver.addHornClause(consArr(doubletonIj, doubletonJk), doubletonIk);
					mSolver.addHornClause(consArr(doubletonJk, doubletonIk), doubletonIj);
					mSolver.addHornClause(consArr(doubletonIk, doubletonIj), doubletonJk);
					mNumberClausesTransitivity += THREE;
				}
				checkTimeout();
			}
		}
	}
	
	@SuppressWarnings({ "unchecked", "squid:S923" })
	private Doubleton<STATE>[] consArr(final Doubleton<STATE>... doubletons) {
		return doubletons;
	}
	
	@SuppressWarnings("unchecked")
	private Doubleton<STATE>[] consArr(final Collection<Doubleton<STATE>> doubletons) {
		return doubletons.toArray(new Doubleton[doubletons.size()]);
	}
	
	private static <T> boolean voidOfNull(final T[] positiveAtoms) {
		for (final T elem : positiveAtoms) {
			if (elem == null) {
				return false;
			}
		}
		return true;
	}
	
	private void checkTimeout() throws AutomataOperationCanceledException {
		if (isCancellationRequested()) {
			final String taskDescription = NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(
					mOperand, mInitialEquivalenceClasses);
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(), taskDescription);
			throw new AutomataOperationCanceledException(rti);
		}
	}

}
