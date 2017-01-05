/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * Partial Max-SAT based minimization of NWA using symmetric pairs ({@link Doubleton}s) of states as variable type.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see MinimizeNwaMaxSat2
 */
public class MinimizeNwaPmaxSatDoubleton<LETTER, STATE> extends MinimizeNwaMaxSat2<LETTER, STATE, Doubleton<STATE>> {
	@SuppressWarnings("rawtypes")
	private static final Doubleton[] EMPTY_LITERALS = new Doubleton[0];
	private static final int THREE = 3;
	
	private final Iterable<Set<STATE>> mInitialPartition;
	private final int mLargestBlockInitialPartition;
	private final int mInitialPartitionSize;
	
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
	public MinimizeNwaPmaxSatDoubleton(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, Collections.singleton(operand.getStates()), new Settings<>());
	}
	
	/**
	 * Constructor with an initial partition.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param initialPartition
	 *            We only try to merge states that are in one of the blocks.
	 * @param settings
	 *            settings wrapper
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaPmaxSatDoubleton(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final Collection<Set<STATE>> initialPartition,
			final Settings<STATE> settings) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, initialPartition, settings, true);
	}
	
	/**
	 * Constructor with an initial partition.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param initialPartition
	 *            We only try to merge states that are in one of the blocks.
	 * @param settings
	 *            settings wrapper
	 * @param applyInitialPartitionPreprocessing
	 *            {@code true} iff preprocessing of the initial partition should be applied
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaPmaxSatDoubleton(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final Collection<Set<STATE>> initialPartition,
			final Settings<STATE> settings, final boolean applyInitialPartitionPreprocessing)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, operand, settings);
		
		mInitialPartition = applyInitialPartitionPreprocessing
				? new LookaheadPartitionConstructor<>(services, operand, initialPartition,
						mSettings.getFinalStateConstraints()).getPartition()
				: initialPartition;
		int largestBlockInitialPartition = 0;
		int initialPartitionSize = 0;
		for (final Set<STATE> equivalenceClass : mInitialPartition) {
			for (final STATE state : equivalenceClass) {
				mState2EquivalenceClass.put(state, equivalenceClass);
			}
			largestBlockInitialPartition = Math.max(largestBlockInitialPartition, equivalenceClass.size());
			++initialPartitionSize;
		}
		mLargestBlockInitialPartition = largestBlockInitialPartition;
		mInitialPartitionSize = initialPartitionSize;
		mLogger.info("Initial partition has " + initialPartitionSize + " blocks, largest block has "
				+ largestBlockInitialPartition + " states");
		
		run();
	}
	
	@Override
	protected String createTaskDescription() {
		return NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(
				mOperand, mInitialPartitionSize, mLargestBlockInitialPartition);
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
	
	@Override
	protected void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialPartition) {
			final STATE[] states = constructStateArray(equivalenceClass);
			generateVariablesHelper(states);
			checkTimeout(GENERATING_VARIABLES);
		}
	}
	
	private void generateVariablesHelper(final STATE[] states) {
		if (states.length <= 1) {
			return;
		}
		
		final boolean separateFinalAndNonfinalStates = mSettings.getFinalStateConstraints();
		
		for (int i = 0; i < states.length; i++) {
			final STATE stateI = states[i];
			
			// add to transitivity generator
			if (mTransitivityGenerator != null) {
				mTransitivityGenerator.addContent(stateI);
			}
			
			for (int j = 0; j < i; j++) {
				final STATE stateJ = states[j];
				final Doubleton<STATE> doubleton = new Doubleton<>(stateI, stateJ);
				mStatePairs.put(stateI, stateJ, doubleton);
				mStatePairs.put(stateJ, stateI, doubleton);
				mSolver.addVariable(doubleton);
				
				// separate final and nonfinal states
				if (separateFinalAndNonfinalStates && (mOperand.isFinal(stateI) ^ mOperand.isFinal(stateJ))) {
					setStatesDifferent(doubleton);
					mNumberClausesAcceptance++;
				}
			}
		}
	}
	
	/**
	 * Tells the solver that two states are different.
	 */
	@SuppressWarnings("unchecked")
	private void setStatesDifferent(final Doubleton<STATE> doubleton) {
		mSolver.addHornClause(new Doubleton[] { doubleton }, null);
	}
	
	@Override
	protected void generateTransitionConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialPartition) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i = 0; i < states.length; i++) {
				generateTransitionConstraintsHelper(states, i);
				checkTimeout(ADDING_TRANSITION_CONSTRAINTS);
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
				setStatesDifferent(mStatePairs.get(state1, state2));
				
				// all corresponding clauses are trivially true
				continue;
			}
			
			final boolean predPairKnowToBeSimilar = knownToBeSimilar(state1, state2);
			
			final Doubleton<STATE> predDoubleton = getDoubleton(state1, state2, predPairKnowToBeSimilar);
			
			if (mSettings.getUseTransitionHornClauses()) {
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
				if (mSettings.getUseTransitionHornClauses()) {
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
				if (mSettings.getUseTransitionHornClauses()) {
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
				generateTransitionConstraintGeneralReturnHelperSymmetric(linPredDoubleton, hierPredDoubleton, succs1,
						succs2);
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
	
	@Override
	protected void generateTransitivityConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialPartition) {
			final STATE[] states = constructStateArray(equivalenceClass);
			generateTransitivityConstraintsHelper(states);
		}
	}
	
	@SuppressWarnings("unchecked")
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
					mSolver.addHornClause(new Doubleton[] { doubletonIj, doubletonJk }, doubletonIk);
					mSolver.addHornClause(new Doubleton[] { doubletonJk, doubletonIk }, doubletonIj);
					mSolver.addHornClause(new Doubleton[] { doubletonIk, doubletonIj }, doubletonJk);
					mNumberClausesTransitivity += THREE;
				}
				checkTimeout(ADDING_TRANSITIVITY_CONSTRAINTS);
			}
		}
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
				(predDoubleton == null) ? EMPTY_LITERALS : (new Doubleton[] { predDoubleton });
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
				negativeAtoms = EMPTY_LITERALS;
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
		assert isVoidOfNull(negativeAtoms) && isVoidOfNull(positiveAtoms) : "Array/list must be void of null elements.";
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
			mSolver.addHornClause(EMPTY_LITERALS, positiveAtom);
		} else {
			mSolver.addHornClause(new Doubleton[] { negativeAtom }, positiveAtom);
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
			mSolver.addHornClause(new Doubleton[] { negativeAtom1, negativeAtom2 }, positiveAtom);
			mNumberClausesTransitions++;
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
		return flag ? null : mStatePairs.get(state1, state2);
	}
	
	@SuppressWarnings("unchecked")
	private Doubleton<STATE>[] consArr(final Collection<Doubleton<STATE>> doubletons) {
		return doubletons.toArray(new Doubleton[doubletons.size()]);
	}
	
	@Override
	protected UnionFind<STATE> constructEquivalenceClasses() throws AssertionError {
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
}
