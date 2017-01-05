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

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.DimacsMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.GeneralMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.HornMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.TransitivityGeneralMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.VariableStatus;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDirectSimulationB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Partial Max-SAT based minimization of NWA.<br>
 * This class feeds an {@link AbstractMaxSatSolver} with clauses based on information from an input, e.g.,
 * {@link ReduceNwaDirectSimulationB}. If there is no input, a {@link LookaheadPartitionConstructor} is used.
 * <p>
 * For small deterministic NWA it produces small results efficiently. For large NWA it runs out of memory.
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
 * @param <T>
 *            variable type used in the solver
 */
public abstract class MinimizeNwaMaxSat2<LETTER, STATE, T> extends AbstractMinimizeNwaDd<LETTER, STATE> {
	protected static final String GENERATING_VARIABLES = "generating variables";
	protected static final String ADDING_TRANSITION_CONSTRAINTS = "adding transition constraints";
	protected static final String ADDING_TRANSITIVITY_CONSTRAINTS = "adding transitivity constraints";
	protected static final String SOLVER_TIMEOUT = "solving";
	
	protected final NestedMap2<STATE, STATE, T> mStatePairs = new NestedMap2<>();
	protected final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	protected final Settings<STATE> mSettings;
	protected final AbstractMaxSatSolver<T> mSolver;
	protected ScopedTransitivityGenerator<STATE> mTransitivityGenerator;
	
	protected int mNumberClausesAcceptance;
	protected int mNumberClausesTransitions;
	protected int mNumberClausesTransitionsNondeterministic;
	protected int mNumberClausesTransitivity;
	
	protected long mTimer;
	protected long mTimePreprocessing;
	protected long mTimeSolving;
	
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
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	protected MinimizeNwaMaxSat2(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final Settings<STATE> settings)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, "minimizeNwaMaxSat2", operand);
		mTimer = System.currentTimeMillis();
		mOperand = operand;
		mSettings = settings;
		mSettings.validate();
		
		// create solver
		switch (mSettings.getSolverMode()) {
			case EXTERNAL:
				mSolver = new DimacsMaxSatSolver<>(mServices);
				break;
			case HORN:
				mSolver = new HornMaxSatSolver<>(mServices);
				break;
			case TRANSITIVITY:
				// we can omit transitivity clauses if the operand has no return transitions
				mSolver = mOperand.getReturnAlphabet().isEmpty()
						? new GeneralMaxSatSolver<>(mServices)
						: createTransitivitySolver();
				break;
			case GENERAL:
				mSolver = new GeneralMaxSatSolver<>(mServices);
				break;
			default:
				throw new IllegalArgumentException("Unknown solver mode: " + mSettings.getSolverMode());
		}
	}
	
	@SuppressWarnings("rawtypes")
	private TransitivityGeneralMaxSatSolver createTransitivitySolver() {
		mTransitivityGenerator = new ScopedTransitivityGenerator<>(mSettings.mUsePathCompression);
		return new TransitivityGeneralMaxSatSolver<>(mServices, mTransitivityGenerator);
	}
	
	protected final void run() throws AutomataOperationCanceledException {
		feedSolver();
		
		mTimePreprocessing = mTimer;
		mTimer = System.currentTimeMillis();
		mTimePreprocessing = mTimer - mTimePreprocessing;
		
		constructResult(mSettings.isAddMapOldState2newState());
		
		mTimeSolving = mTimer;
		mTimer = System.currentTimeMillis();
		mTimeSolving = mTimer - mTimeSolving;
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}
	
	private void feedSolver() throws AutomataOperationCanceledException {
		generateVariablesAndAcceptingConstraints();
		generateTransitionConstraints();
		if (mTransitivityGenerator == null) {
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
		final UnionFind<STATE> resultingEquivalenceClasses = constructEquivalenceClasses();
		constructResultFromUnionFind(resultingEquivalenceClasses, addMapOldState2newState);
	}
	
	protected abstract void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException;
	
	protected abstract void generateTransitionConstraints() throws AutomataOperationCanceledException;
	
	protected abstract void generateTransitivityConstraints() throws AutomataOperationCanceledException;
	
	protected abstract UnionFind<STATE> constructEquivalenceClasses() throws AssertionError;
	
	protected abstract boolean knownToBeSimilar(final STATE state1, final STATE state2);
	
	protected abstract boolean knownToBeDifferent(final STATE state1, final STATE state2);
	
	protected abstract String createTaskDescription();
	
	@SuppressWarnings("unchecked")
	protected final STATE[] constructStateArray(final Collection<STATE> states) {
		return states.toArray((STATE[]) new Object[states.size()]);
	}
	
	/**
	 * @return {@code true} iff two states have the same outgoing internal and call symbols.
	 */
	protected final boolean haveSameOutgoingInternalCallSymbols(final STATE predState1, final STATE predState2) {
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
	protected final boolean haveSameOutgoingReturnSymbols(final STATE up1, final STATE down1, final STATE up2,
			final STATE down2) {
		return getSameOutgoingReturnSymbols(up1, down1, up2, down2) != null;
	}
	
	/**
	 * @return A set of letters iff the two states have the same outgoing return symbols with respect to the
	 *         hierarchical predecessors, {@code null} otherwise.
	 */
	protected final Set<LETTER> getSameOutgoingReturnSymbols(final STATE up1, final STATE down1, final STATE up2,
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
	
	protected final VariableStatus resultFromSolver(final STATE state1, final STATE state2) {
		final T doubleton = mStatePairs.get(state1, state2);
		return mSolver.getValue(doubleton);
	}
	
	protected static final <T> boolean isVoidOfNull(final T[] positiveAtoms) {
		for (final T elem : positiveAtoms) {
			if (elem == null) {
				return false;
			}
		}
		return true;
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
		
		if (mTimePreprocessing != 0L) {
			builder.append(". Preprocessing time ").append(mTimePreprocessing);
		}
		if (mTimeSolving != 0L) {
			builder.append(". Solving time ").append(mTimeSolving);
		}
		
		return new RunningTaskInfo(getClass(), builder.toString());
	}
	
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = super.getAutomataOperationStatistics();
		if (mTimePreprocessing != 0L) {
			statistics.addKeyValuePair(StatisticsType.TIME_PREPROCESSING, mTimePreprocessing);
		}
		if (mTimeSolving != 0L) {
			statistics.addKeyValuePair(StatisticsType.TIME_SOLVING, mTimeSolving);
		}
		statistics.addKeyValuePair(StatisticsType.NUMBER_OF_VARIABLES, mSolver.getNumberOfVariables());
		statistics.addKeyValuePair(StatisticsType.NUMBER_OF_CLAUSES, mSolver.getNumberOfClauses());
		return statistics;
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
		 * Add constraints that final and non-final states cannot be merged.
		 */
		private boolean mUseFinalStateConstraints = true;
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
		
		public Settings() {
			// default constructor
		}
		
		/**
		 * Validates the settings object for inconsistencies.
		 */
		public void validate() {
			if (mSolverMode == null) {
				throw new IllegalArgumentException("No solver mode set.");
			}
			if (!mUseTransitionHornClauses && mSolverMode == SolverMode.HORN) {
				throw new IllegalArgumentException(
						"For using the Horn solver you must use Horn clauses.");
			}
		}
		
		public boolean isAddMapOldState2newState() {
			return mAddMapOldState2newState;
		}
		
		public Settings<STATE> setAddMapOldState2NewState(final boolean value) {
			mAddMapOldState2newState = value;
			return this;
		}
		
		public boolean getFinalStateConstraints() {
			return mUseFinalStateConstraints;
		}
		
		public Settings<STATE> setFinalStateConstraints(final boolean value) {
			mUseFinalStateConstraints = value;
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
	}
}
