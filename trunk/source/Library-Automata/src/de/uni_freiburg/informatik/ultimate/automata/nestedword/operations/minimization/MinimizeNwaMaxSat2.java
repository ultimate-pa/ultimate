/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.DimacsMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.GeneralMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.HornMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.VariableStatus;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDirectSimulationB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IPartition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Partial Max-SAT based minimization of NWA.<br>
 * This class feeds an {@link AbstractMaxSatSolver} with clauses based on information from an input, e.g.,
 * {@link ReduceNwaDirectSimulationB}. If there is no input, a {@link LookaheadPartitionConstructor} is used.
 * <p>
 * For small deterministic NWA it produces small results efficiently. For large NWA it runs out of memory.
 * <p>
 * TODO For generating nondeterministic clauses, the order of the arguments is not specified. Hence we might want to
 * rearrange state1 and state2 such that we have either few long clauses or many short clauses (for all types of
 * transitions).
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <T>
 *            variable type used in the solver
 */
public abstract class MinimizeNwaMaxSat2<LETTER, STATE, T> extends AbstractMinimizeNwaDd<LETTER, STATE> {
	protected static final int THREE = 3;
	protected static final String GENERATING_VARIABLES = "generating variables";
	protected static final String ADDING_TRANSITION_CONSTRAINTS = "adding transition constraints";
	protected static final String ADDING_TRANSITIVITY_CONSTRAINTS = "adding transitivity constraints";
	protected static final String SOLVER_TIMEOUT = "solving";

	protected final NestedMap2<STATE, STATE, T> mStatePair2Var;
	protected final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	protected final Settings<STATE> mSettings;
	protected final AbstractMaxSatSolver<T> mSolver;
	protected ScopedTransitivityGenerator<T, STATE> mTransitivityGenerator;

	private int mNumberClausesAcceptance;
	private int mNumberClausesTransitions;
	private int mNumberClausesTransitionsNondeterministic;
	private int mNumberClausesTransitivity;

	private long mTimer;
	private long mTimeAsserting;
	private long mTimeSolving;

	private long mNumberOfResultPairs;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param partitionPairsWrapper
	 *            result from {@link LookaheadPartitionConstructor}
	 * @param settings
	 *            settings wrapper
	 * @param statePair2Var
	 *            mapping from two states to solver variable
	 * @param libraryMode
	 *            {@code true} iff solver is called by another operation
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	protected MinimizeNwaMaxSat2(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Settings<STATE> settings, final NestedMap2<STATE, STATE, T> statePair2Var)
			throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mTimer = System.currentTimeMillis();
		mOperand = operand;
		mStatePair2Var = statePair2Var;
		mSettings = settings;
		mSettings.validate(mOperand);
		mSolver = createSolver();
	}

	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	private AbstractMaxSatSolver<T> createSolver() {
		switch (mSettings.getSolverMode()) {
			case EXTERNAL:
				return new DimacsMaxSatSolver<>(mServices);
			case HORN:
				return new HornMaxSatSolver<>(mServices);
			case TRANSITIVITY:
				if (hasNoReturnTransitions(mOperand)) {
					// we can omit transitivity clauses if the operand has no return transitions
					return new GeneralMaxSatSolver<>(mServices);
				}
				return createTransitivitySolver();
			case GENERAL:
				return new GeneralMaxSatSolver<>(mServices);
			default:
				throw new IllegalArgumentException("Unknown solver mode: " + mSettings.getSolverMode());
		}
	}

	protected final void run() throws AutomataOperationCanceledException {
		feedSolver();

		mTimeAsserting = mTimer;
		mTimer = System.currentTimeMillis();
		mTimeAsserting = mTimer - mTimeAsserting;

		constructResult(mSettings.isAddMapOldState2newState());

		mTimeSolving = mTimer;
		mTimer = System.currentTimeMillis();
		mTimeSolving = mTimer - mTimeSolving;
	}

	private void feedSolver() throws AutomataOperationCanceledException {
		generateVariablesAndAcceptingConstraints();
		final boolean addTransitivityConstraints = mTransitivityGenerator == null && !hasNoReturnTransitions(mOperand);
		generateTransitionAndTransitivityConstraints(addTransitivityConstraints);
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Number of clauses for: -> acceptance: " + mNumberClausesAcceptance + ", -> transitions: "
					+ mNumberClausesTransitions + ", -> nondeterministic transitions: "
					+ mNumberClausesTransitionsNondeterministic + ", -> transitivity: " + mNumberClausesTransitivity);
		}
	}

	private void constructResult(final boolean addMapOldState2newState)
			throws AutomataOperationCanceledException, AssertionError {
		final boolean satisfiable;
		try {
			satisfiable = mSolver.solve();
		} catch (final AutomataOperationCanceledException e) {
			final RunningTaskInfo rti = getRunningTaskInfo(SOLVER_TIMEOUT);
			e.addRunningTaskInfo(rti);
			throw e;
		}
		if (!satisfiable) {
			throw new AssertionError("Constructed constraints were unsatisfiable");
		}
		final IPartition<STATE> resultPartition = constructResultEquivalenceClasses();
		mNumberOfResultPairs = countNumberOfPairs(resultPartition);
		constructResultFromPartition(resultPartition, addMapOldState2newState);
	}

	private long countNumberOfPairs(final IPartition<STATE> resultPartition) {
		long result = 0;
		for (final Set<STATE> block : resultPartition) {
			result += ((long) block.size()) * ((long) block.size()) - block.size();
		}
		return result;
	}

	protected abstract AbstractMaxSatSolver<T> createTransitivitySolver();

	protected abstract void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException;

	protected abstract void generateTransitionAndTransitivityConstraints(boolean addTransitivityConstraints)
			throws AutomataOperationCanceledException;

	protected abstract IPartition<STATE> constructResultEquivalenceClasses() throws AssertionError;

	protected abstract boolean isInitialPair(STATE state1, STATE state2);

	protected abstract boolean isInitialPair(T pair);

	protected abstract T[] getEmptyVariableArray();

	protected abstract String createTaskDescription();

	@SuppressWarnings("unchecked")
	protected final STATE[] constructStateArray(final Collection<STATE> states) {
		return states.toArray((STATE[]) new Object[states.size()]);
	}

	protected final void generateTransitionConstraintsHelper(final STATE state1, final STATE state2, final T pair) {
		if (knownToBeDifferent(state1, state2, pair)) {
			// all corresponding clauses are trivially true
			return;
		}

		if (mSettings.getUseInternalCallConstraints() && !haveSameOutgoingInternalCallSymbols(state1, state2)) {
			// not known to be different, report to the solver
			setVariableFalse(pair);

			// all corresponding clauses are trivially true
			return;
		}

		final STATE[] downStates1 = getDownStatesArray(state1);
		final T predPair = knownToBeSimilar(state1, state2, pair) ? null : pair;

		// add transition constraints
		if (mSettings.getUseTransitionHornClauses()) {
			generateTransitionConstraintInternalHorn(state1, state2, predPair);
			generateTransitionConstraintCallHorn(state1, state2, predPair);
		} else {
			generateTransitionConstraintInternalGeneral(state1, state2, predPair);
			generateTransitionConstraintCallGeneral(state1, state2, predPair);
		}
		generateTransitionConstraintsHelperReturnMixedLinPred(state1, downStates1, state2, predPair);
	}

	private void generateTransitionConstraintInternalHorn(final STATE predState1, final STATE predState2,
			final T predPair) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans1 : mOperand.internalSuccessors(predState1)) {
			final STATE succState1 = trans1.getSucc();
			for (final OutgoingInternalTransition<LETTER, STATE> trans2 : mOperand.internalSuccessors(predState2,
					trans1.getLetter())) {
				final STATE succState2 = trans2.getSucc();
				generateBinaryTransitionConstraint(predPair, succState1, succState2);
			}
		}
	}

	private void generateTransitionConstraintInternalGeneral(final STATE predState1, final STATE predState2,
			final T predPair) {
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
			generateTransitionConstraintGeneralInternalCallHelper(predPair, succs1, succs2);
		}
	}

	private void generateTransitionConstraintCallHorn(final STATE predState1, final STATE predState2,
			final T predPair) {
		for (final OutgoingCallTransition<LETTER, STATE> trans1 : mOperand.callSuccessors(predState1)) {
			final STATE succState1 = trans1.getSucc();
			for (final OutgoingCallTransition<LETTER, STATE> trans2 : mOperand.callSuccessors(predState2,
					trans1.getLetter())) {
				final STATE succState2 = trans2.getSucc();
				generateBinaryTransitionConstraint(predPair, succState1, succState2);
			}
		}
	}

	private void generateTransitionConstraintCallGeneral(final STATE predState1, final STATE predState2,
			final T predPair) {
		// NOTE: We exploit the knowledge that the states have the same outgoing symbols
		for (final LETTER letter : mOperand.lettersCall(predState1)) {
			final Set<STATE> succs1 = new LinkedHashSet<>();
			final Set<STATE> succs2 = new LinkedHashSet<>();
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(predState1, letter)) {
				succs1.add(trans.getSucc());
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(predState2, letter)) {
				succs2.add(trans.getSucc());
			}
			generateTransitionConstraintGeneralInternalCallHelper(predPair, succs1, succs2);
		}
	}

	protected abstract void generateTransitionConstraintGeneralInternalCallHelper(final T predPair,
			final Set<STATE> succs1, final Set<STATE> succs2);

	protected final void generateTransitionConstraintGeneralInternalCallHelperOneSide(final T predPair,
			final Iterable<STATE> succs1, final Iterable<STATE> succs2, final Collection<STATE> succsToRemove) {
		boolean ignoreConstraint = false;
		for (final STATE succState1 : succs1) {
			for (final STATE succState2 : succs2) {
				if (knownToBeSimilar(succState1, succState2, null)) {
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
				generateNaryTransitionConstraint(predPair, succState1, succs2);
			}
		}
	}

	private void generateTransitionConstraintsHelperReturnMixedLinPred(final STATE state1, final STATE[] downStates1,
			final STATE state2, final T predPair) {
		// NOTE: slower iteration outside
		for (final STATE down2 : mOperand.getDownStates(state2)) {
			for (final STATE down1 : downStates1) {
				generateTransitionConstraintReturn(state1, state2, predPair, down1, down2,
						mSettings.getUseTransitionHornClauses(), true);
			}
		}
	}

	protected final void generateTransitionConstraintsHelperReturnSameLinPred(final STATE state,
			final STATE[] downStates) {
		for (int k = 0; k < downStates.length; k++) {
			for (int l = 0; l < k; l++) {
				generateTransitionConstraintReturn(state, state, null, downStates[k], downStates[l],
						mSettings.getUseTransitionHornClauses(), false);
			}
		}
	}

	private void generateTransitionConstraintReturn(final STATE linPredState1, final STATE linPredState2,
			final T linPredPair, final STATE hierPredState1, final STATE hierPredState2, final boolean horn,
			final boolean useSubclassSpecificMethod) {
		if (knownToBeDifferent(hierPredState1, hierPredState2, null)) {
			// all corresponding clauses are trivially true
			return;
		}

		final T hierPredPair = getVariableIfNotSimilar(hierPredState1, hierPredState2);
		final Set<LETTER> sameOutgoingReturnSymbols =
				getSameOutgoingReturnSymbols(linPredState1, hierPredState1, linPredState2, hierPredState2);
		if (sameOutgoingReturnSymbols == null) {
			addThreeLiteralHornClause(linPredPair, hierPredPair, null);
			return;
		}

		// both DoubleDeckers have same outgoing return symbols
		if (horn) {
			generateTransitionConstraintReturnHelperHorn(linPredState1, linPredState2, linPredPair, hierPredState1,
					hierPredState2, hierPredPair);
		} else {
			generateTransitionConstraintReturnHelperGeneral(linPredState1, linPredState2, linPredPair, hierPredState1,
					hierPredState2, hierPredPair, sameOutgoingReturnSymbols, useSubclassSpecificMethod);
		}
	}

	private void generateTransitionConstraintReturnHelperHorn(final STATE linPredState1, final STATE linPredState2,
			final T linPredPair, final STATE hierPredState1, final STATE hierPredState2, final T hierPredPair) {
		for (final OutgoingReturnTransition<LETTER, STATE> trans1 : mOperand.returnSuccessorsGivenHier(linPredState1,
				hierPredState1)) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans2 : mOperand.returnSuccessors(linPredState2,
					hierPredState2, trans1.getLetter())) {
				if (knownToBeSimilar(trans1.getSucc(), trans2.getSucc(), null)) {
					// clause is trivially true, continue with next state
					break;
				}
				final T succPair = getVariableIfNotDifferent(trans1.getSucc(), trans2.getSucc());
				addThreeLiteralHornClause(linPredPair, hierPredPair, succPair);
			}
		}
	}

	private void generateTransitionConstraintReturnHelperGeneral(final STATE linPredState1, final STATE linPredState2,
			final T linPredPair, final STATE hierPredState1, final STATE hierPredState2, final T hierPredPair,
			final Set<LETTER> sameOutgoingReturnSymbols, final boolean useSubclassSpecificMethod) {
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
			if (useSubclassSpecificMethod) {
				generateTransitionConstraintGeneralReturnHelper(linPredPair, hierPredPair, succs1, succs2);
			} else {
				generateTransitionConstraintGeneralReturnHelperSymmetric(linPredPair, hierPredPair, succs1, succs2);
			}
		}
	}

	protected abstract void generateTransitionConstraintGeneralReturnHelper(final T linPredPair, final T hierPredPair,
			final Set<STATE> succs1, final Set<STATE> succs2);

	/**
	 * NOTE: This method can also be used in {@link MinimizeNwaPmaxSatDirect} because it is necessary for
	 * correctness.
	 */
	protected final void generateTransitionConstraintGeneralReturnHelperSymmetric(final T linPredPair,
			final T hierPredPair, final Set<STATE> succs1, final Set<STATE> succs2) {
		// symmetric handling (in both directions)

		final Collection<STATE> succsToRemove = new ArrayList<>();

		generateTransitionConstraintGeneralReturnHelperOneSide(linPredPair, hierPredPair, succs1, succs2,
				succsToRemove);
		/*
		 * Optimization: If a state from the second set is known to be similar to another one from the first set, we
		 * should not try to add a clause for the other direction (as it will be found out again that they are
		 * similar).
		 */
		succs2.removeAll(succsToRemove);

		generateTransitionConstraintGeneralReturnHelperOneSide(linPredPair, hierPredPair, succs2, succs1, null);
	}

	protected final void generateTransitionConstraintGeneralReturnHelperOneSide(final T linPredPair,
			final T hierPredPair, final Set<STATE> succs1, final Set<STATE> succs2,
			final Collection<STATE> succsToRemove) {
		boolean ignore = false;
		for (final STATE succState1 : succs1) {
			for (final STATE succState2 : succs2) {
				if (knownToBeSimilar(succState1, succState2, null)) {
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
				generateNaryTransitionConstraint(linPredPair, hierPredPair, succState1, succs2);
			}
		}
	}

	private void addIfNotNull(final Collection<STATE> collection, final STATE element) {
		if (collection != null) {
			collection.add(element);
		}
	}

	private void generateBinaryTransitionConstraint(final T predpair, final STATE succState1, final STATE succState2) {
		// first check whether the clause is trivially true
		if (knownToBeSimilar(succState1, succState2, null)) {
			return;
		}

		final T succPair = getVariableIfNotDifferent(succState1, succState2);
		addTwoLiteralHornClause(predpair, succPair);
	}

	@SuppressWarnings("unchecked")
	private void generateNaryTransitionConstraint(final T predpair, final STATE succState1,
			final Iterable<STATE> succStates2) {
		final List<T> succPairs = new ArrayList<>();
		for (final STATE succState2 : succStates2) {
			if (!knownToBeDifferent(succState1, succState2, null)) {
				final T succPair = getVariable(succState1, succState2, false);
				succPairs.add(succPair);
			}
		}
		final T[] negativeAtoms = (predpair == null) ? getEmptyVariableArray() : (T[]) (new Object[] { predpair });
		final T[] positiveAtoms = consArr(succPairs);
		addArbitraryLiteralClause(negativeAtoms, positiveAtoms);
	}

	@SuppressWarnings("unchecked")
	private void generateNaryTransitionConstraint(final T linPredPair, final T hierPredPair, final STATE succState1,
			final Iterable<STATE> succStates2) {
		final List<T> succPairs = new ArrayList<>();
		for (final STATE succState2 : succStates2) {
			if (!knownToBeDifferent(succState1, succState2, null)) {
				final T succPair = getVariable(succState1, succState2, false);
				succPairs.add(succPair);
			}
		}

		final T[] negativeAtoms;
		if (linPredPair == null) {
			if (hierPredPair == null) {
				negativeAtoms = getEmptyVariableArray();
			} else {
				negativeAtoms = (T[]) new Object[] { hierPredPair };
			}
		} else {
			if (hierPredPair == null) {
				negativeAtoms = (T[]) new Object[] { linPredPair };
			} else {
				negativeAtoms = (T[]) new Object[] { linPredPair, hierPredPair };
			}
		}
		final T[] positiveAtoms = consArr(succPairs);
		addArbitraryLiteralClause(negativeAtoms, positiveAtoms);
	}

	@SuppressWarnings("unchecked")
	protected final void addTransitivityClausesToSolver(final T pair12, final T pair23, final T pair13) {
		mSolver.addHornClause((T[]) new Object[] { pair12, pair23 }, pair13);
		mSolver.addHornClause((T[]) new Object[] { pair23, pair13 }, pair12);
		mSolver.addHornClause((T[]) new Object[] { pair13, pair12 }, pair23);
		mNumberClausesTransitivity += THREE;
	}

	protected final boolean knownToBeSimilar(final STATE state1, final STATE state2, final T pair) {
		if (state1.equals(state2)) {
			return true;
		}
		if (pair == null) {
			if (isInitialPair(state1, state2)) {
				return resultFromSolver(state1, state2) == VariableStatus.TRUE;
			}
		} else {
			if (isInitialPair(pair)) {
				return resultFromSolver(pair) == VariableStatus.TRUE;
			}
		}
		return false;
	}

	protected final boolean knownToBeDifferent(final STATE state1, final STATE state2, final T pair) {
		if (state1.equals(state2)) {
			return false;
		}
		if (pair == null) {
			if (isInitialPair(state1, state2)) {
				return resultFromSolver(state1, state2) == VariableStatus.FALSE;
			}
		} else {
			if (isInitialPair(pair)) {
				return resultFromSolver(pair) == VariableStatus.FALSE;
			}
		}
		return true;
	}

	protected final STATE[] getDownStatesArray(final STATE state) {
		return constructStateArray(mOperand.getDownStates(state));
	}

	@SuppressWarnings("unchecked")
	protected final T[] consArr(final Collection<T> pairs) {
		return (T[]) pairs.toArray(new Object[pairs.size()]);
	}

	protected final void setStatesDifferent(final T pair) {
		setVariableFalse(pair);
		mNumberClausesAcceptance++;
	}

	@SuppressWarnings("unchecked")
	protected final void addInverseHornClause(final T negativeAtom, final Collection<T> positiveAtoms) {
		addArbitraryLiteralClause((T[]) (new Object[] { negativeAtom }), consArr(positiveAtoms));
	}

	private void addArbitraryLiteralClause(final T[] negativeAtoms, final T[] positiveAtoms) {
		assert isVoidOfNull(negativeAtoms) && isVoidOfNull(positiveAtoms) : "Array/list must be void of null elements.";
		assert (negativeAtoms.length == 1) || (negativeAtoms.length == 2) : "Always pass one or two negative atoms.";
		if (positiveAtoms.length <= 1) {
			// deterministic case
			final T positiveAtom = (positiveAtoms.length == 1) ? positiveAtoms[0] : null;
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
	private void addTwoLiteralHornClause(final T negativeAtom, final T positiveAtom) {
		if (negativeAtom == null) {
			if (positiveAtom == null) {
				throw new AssertionError("clause must not be empty");
			}
			mSolver.addHornClause(getEmptyVariableArray(), positiveAtom);
		} else {
			mSolver.addHornClause((T[]) new Object[] { negativeAtom }, positiveAtom);
		}
		mNumberClausesTransitions++;
	}

	@SuppressWarnings("unchecked")
	private void addThreeLiteralHornClause(final T negativeAtom1, final T negativeAtom2, final T positiveAtom) {
		if (negativeAtom1 == null) {
			addTwoLiteralHornClause(negativeAtom2, positiveAtom);
		} else if (negativeAtom2 == null) {
			addTwoLiteralHornClause(negativeAtom1, positiveAtom);
		} else {
			mSolver.addHornClause((T[]) new Object[] { negativeAtom1, negativeAtom2 }, positiveAtom);
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
		if (!testOutgoingSymbols(letters1, letters2)) {
			return false;
		}

		// call symbols
		letters1 = mOperand.lettersCall(predState1);
		letters2 = mOperand.lettersCall(predState2);
		return testOutgoingSymbols(letters1, letters2);
	}

	/**
	 * @param letters1
	 *            Outgoing letters of first state.
	 * @param letters2
	 *            outgoing letters of second state
	 * @return {@code true} iff test for valid outgoing symbols succeeds, i.e., no objection was found
	 */
	protected abstract boolean testOutgoingSymbols(Set<LETTER> letters1, Set<LETTER> letters2);

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

	private VariableStatus resultFromSolver(final STATE state1, final STATE state2) {
		return resultFromSolver(getVariable(state1, state2, false));
	}

	private VariableStatus resultFromSolver(final T pair) {
		return mSolver.getValue(pair);
	}

	/**
	 * Getter for a {@link T}.
	 * 
	 * @param state1
	 *            state 1
	 * @param state2
	 *            state 2
	 * @param flag
	 *            {@code true} iff {@code null} should be returned
	 * @return pair of two states iff the flag is not {@code true}, {@code null} otherwise
	 */
	protected final T getVariable(final STATE state1, final STATE state2, final boolean flag) {
		return flag ? null : mStatePair2Var.get(state1, state2);
	}

	/**
	 * @return {@code null} if states are different, pair variable otherwise.
	 */
	private T getVariableIfNotDifferent(final STATE state1, final STATE state2) {
		return getVariable(state1, state2, knownToBeDifferent(state1, state2, null));
	}

	/**
	 * @return {@code null} if states are similar, pair variable otherwise.
	 */
	private T getVariableIfNotSimilar(final STATE state1, final STATE state2) {
		return getVariable(state1, state2, knownToBeSimilar(state1, state2, null));
	}

	/**
	 * Tells the solver that two states are different.
	 */
	@SuppressWarnings("unchecked")
	private void setVariableFalse(final T pair) {
		mSolver.addHornClause((T[]) new Object[] { pair }, null);
	}

	private static <T> boolean isVoidOfNull(final T[] positiveAtoms) {
		for (final T elem : positiveAtoms) {
			if (elem == null) {
				return false;
			}
		}
		return true;
	}

	private static <LETTER, STATE> boolean hasNoReturnTransitions(final IDoubleDeckerAutomaton<LETTER, STATE> operand) {
		return operand.getVpAlphabet().getReturnAlphabet().isEmpty();
	}

	protected final void checkTimeout(final String currentTask) throws AutomataOperationCanceledException {
		if (isCancellationRequested()) {
			final RunningTaskInfo rti = getRunningTaskInfo(currentTask);
			throw new AutomataOperationCanceledException(rti);
		}
	}

	private RunningTaskInfo getRunningTaskInfo(final String currentTask) {
		final StringBuilder builder = new StringBuilder();
		final String taskDescription = createTaskDescription();
		// @formatter:off
		builder.append(taskDescription)
				.append(". Currently ")
				.append(currentTask)
				.append(". Solver was fed with ")
				.append(mSolver.getNumberOfClauses())
				.append(" variables and ")
				.append(mSolver.getNumberOfClauses())
				.append(" clauses");
		// @formatter:on

		if (mTimeAsserting != 0L) {
			builder.append(". Asserting time ").append(mTimeAsserting);
		}
		if (mTimeSolving != 0L) {
			builder.append(". Solving time ").append(mTimeSolving);
		}

		return new RunningTaskInfo(getClass(), builder.toString());
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = super.getAutomataOperationStatistics();
		addStatistics(statistics);
		return statistics;
	}

	/**
	 * @param statistics
	 *            Statistics object.
	 */
	public void addStatistics(final AutomataOperationStatistics statistics) {
		statistics.addKeyValuePair(StatisticsType.TIME_ASSERTING, mTimeAsserting);
		statistics.addKeyValuePair(StatisticsType.TIME_SOLVING, mTimeSolving);
		statistics.addKeyValuePair(StatisticsType.NUMBER_VARIABLES, mSolver.getNumberOfVariables());
		statistics.addKeyValuePair(StatisticsType.NUMBER_CLAUSES, mSolver.getNumberOfClauses());
		statistics.addKeyValuePair(StatisticsType.NUMBER_RESULT_PAIRS, mNumberOfResultPairs);
	}

	@Override
	protected Pair<Boolean, String> checkResultHelper(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return checkLanguageEquivalence(stateFactory);
	}

	/**
	 * Settings wrapper that allows a lean constructor for the user.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <STATE>
	 *            state type
	 */
	public static class Settings<STATE> {
		/**
		 * Solver mode.
		 * 
		 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
		 */
		public enum SolverMode {
			/** External solver. */
			EXTERNAL,
			/** Horn solver. */
			HORN,
			/** Solver with on-demand transitivity support. */
			TRANSITIVITY,
			/** General solver. */
			GENERAL
		}

		/**
		 * Add mapping 'old state -> new state'.
		 */
		private boolean mAddMapOldState2newState;
		/**
		 * Solver mode.
		 */
		private SolverMode mSolverMode = SolverMode.TRANSITIVITY;
		/**
		 * Predicate that controls merging of final and non-final states.
		 * <p>
		 * Returns {@code true} for pairs of states that should not be merged.
		 */
		private BiPredicate<STATE, STATE> mFinalNonfinalConstraintPredicate = new TrueBiPredicate<>();
		/**
		 * Use Horn clauses for transitions. This flag can also be set for nondeterministic automata. However, the
		 * results might not be satisfactory: all successors have to be similar in this case.
		 */
		private boolean mUseTransitionHornClauses;
		/**
		 * Use path compression in the transitivity generator.
		 * <p>
		 * Currently always deactivated.
		 */
		private final boolean mUsePathCompression = false;
		/**
		 * Use constraints for closure under internal/call successors.
		 * <p>
		 * Some users already ensure this fact.
		 */
		private boolean mUseInternalCallConstraints = true;
		/**
		 * {@code true}: Use the solver in library mode (called by others).<br>
		 * {@code false}: Use the solver as standalone operation.
		 */
		private boolean mLibraryMode = true;

		public Settings() {
			// default constructor
		}

		/**
		 * Validates the settings object for inconsistencies.
		 * 
		 * @param operand
		 *            operand
		 * @param <LETTER>
		 *            letter type
		 */
		public <LETTER> void validate(final IDoubleDeckerAutomaton<LETTER, STATE> operand) {
			if (mSolverMode == null) {
				throw new IllegalArgumentException("No solver mode set.");
			}
			if (mSolverMode == SolverMode.HORN) {
				if (!mUseTransitionHornClauses) {
					throw new IllegalArgumentException("For using the Horn solver you must use Horn clauses.");
				}
			}
		}

		public boolean isAddMapOldState2newState() {
			return mAddMapOldState2newState;
		}

		public Settings<STATE> setAddMapOldState2NewState(final boolean value) {
			mAddMapOldState2newState = value;
			return this;
		}

		public BiPredicate<STATE, STATE> getFinalNonfinalConstraintPredicate() {
			return mFinalNonfinalConstraintPredicate;
		}

		public Settings<STATE> setFinalNonfinalConstraintPredicate(final BiPredicate<STATE, STATE> value) {
			mFinalNonfinalConstraintPredicate = value;
			return this;
		}

		public boolean getUseTransitionHornClauses() {
			return mUseTransitionHornClauses;
		}

		public SolverMode getSolverMode() {
			return mSolverMode;
		}

		/**
		 * Sets the solver mode to {@link SolverMode#EXTERNAL}.
		 * 
		 * @return this
		 */
		public Settings<STATE> setSolverModeExternal() {
			mSolverMode = SolverMode.EXTERNAL;
			return this;
		}

		/**
		 * Sets the solver mode to {@link SolverMode#TRANSITIVITY}.
		 * 
		 * @return this
		 */
		public Settings<STATE> setSolverModeTransitivity() {
			mSolverMode = SolverMode.TRANSITIVITY;
			return this;
		}

		/**
		 * Sets the solver mode to {@link SolverMode#GENERAL}.
		 * 
		 * @return this
		 */
		public Settings<STATE> setSolverModeGeneral() {
			mSolverMode = SolverMode.GENERAL;
			return this;
		}

		public boolean getUseInternalCallConstraints() {
			return mUseInternalCallConstraints;
		}

		public Settings<STATE> setUseInternalCallConstraints(final boolean useInternalCallConstraints) {
			mUseInternalCallConstraints = useInternalCallConstraints;
			return this;
		}

		public boolean getLibraryMode() {
			return mLibraryMode;
		}

		public Settings<STATE> setLibraryMode(final boolean mode) {
			mLibraryMode = mode;
			return this;
		}

		public boolean isUsePathCompression() {
			return mUsePathCompression;
		}
	}

	/**
	 * Given a pair of states, returns {@code true}.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public static class TrueBiPredicate<STATE> implements BiPredicate<STATE, STATE> {
		@Override
		public boolean test(final STATE p, final STATE q) {
			return true;
		}
	}

	/**
	 * Given a pair of states, returns {@code true} iff the pair is in the backing relation.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public static class RelationBackedBiPredicate<STATE> implements BiPredicate<STATE, STATE> {
		private final ISetOfPairs<STATE, ?> mRelation;

		/**
		 * @param relation
		 *            Relation of bad pairs of states that should not be merged.
		 */
		public RelationBackedBiPredicate(final ISetOfPairs<STATE, ?> relation) {
			mRelation = relation;
		}

		@Override
		public boolean test(final STATE p, final STATE q) {
			return mRelation.containsPair(p, q);
		}
	}
}
