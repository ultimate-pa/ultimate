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
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.DimacsMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IPartition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Partial Max-SAT based minimization of NWA using {@link Doubleton}s (symmetric pairs) of states as variable type.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see MinimizeNwaMaxSat2
 */
public abstract class MinimizeNwaPmaxSat<LETTER, STATE> extends MinimizeNwaMaxSat2<LETTER, STATE, Doubleton<STATE>> {
	@SuppressWarnings("rawtypes")
	private static final Doubleton[] EMPTY_LITERALS = new Doubleton[0];

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
	public MinimizeNwaPmaxSat(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, new Settings<STATE>().setLibraryMode(false), null);
	}

	/**
	 * Full constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param settings
	 *            settings wrapper
	 * @param applyInitialPartitionPreprocessing
	 *            {@code true} iff preprocessing of the initial partition should be applied
	 * @param libraryMode
	 *            {@code true} iff solver is called by another operation
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaPmaxSat(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Settings<STATE> settings, final String filename)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, operand, settings, new NestedMap2<>(), filename);
	}

	@Override
	protected abstract String createTaskDescription();

	@Override
	public void addStatistics(final AutomataOperationStatistics statistics) {
		super.addStatistics(statistics);
	}

	@Override
	protected abstract void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException;

	protected abstract void generateVariablesHelper(final STATE[] states);

	@Override
	protected abstract void generateTransitionAndTransitivityConstraints(final boolean addTransitivityConstraints) throws AutomataOperationCanceledException;

	protected void generateTransitionConstraints(final STATE[] states, final int firstStateIndex) {
		final STATE state1 = states[firstStateIndex];
		final STATE[] downStates1 = getDownStatesArray(state1);
		for (int j = 0; j < firstStateIndex; j++) {
			final STATE state2 = states[j];

			// add transition constraints
			generateTransitionConstraintsHelper(state1, state2, getVariable(state1, state2, false));
		}
		// add constraints for reflexive pairs; those are not considered above
		generateTransitionConstraintsHelperReturnSameLinPred(state1, downStates1);
	}

	@Override
	protected boolean testOutgoingSymbols(final Set<LETTER> letters1, final Set<LETTER> letters2) {
		return letters1.equals(letters2);
	}

	@Override
	protected void generateTransitionConstraintGeneralInternalCallHelper(final Doubleton<STATE> predPair,
			final Set<STATE> succs1, final Set<STATE> succs2) {
		// symmetric handling (in both directions)

		final Collection<STATE> succsToRemove = new ArrayList<>();

		generateTransitionConstraintGeneralInternalCallHelperOneSide(predPair, succs1, succs2, succsToRemove);
		/*
		 * Optimization: If a state from the second set is known to be similar to another on from the first set, we
		 * should not try to add a clause for the other direction (as it will be found out again that they are
		 * similar).
		 */
		succs2.removeAll(succsToRemove);

		generateTransitionConstraintGeneralInternalCallHelperOneSide(predPair, succs2, succs1, null);
	}

	@Override
	protected void generateTransitionConstraintGeneralReturnHelper(final Doubleton<STATE> linPredPair,
			final Doubleton<STATE> hierPredPair, final Set<STATE> succs1, final Set<STATE> succs2) {
		generateTransitionConstraintGeneralReturnHelperSymmetric(linPredPair, hierPredPair, succs1, succs2);
	}

	protected void generateTransitivityConstraints(final STATE[] states) throws AutomataOperationCanceledException {
		for (int i = 0; i < states.length; i++) {
			for (int j = 0; j < i; j++) {
				for (int k = 0; k < j; k++) {
					final Doubleton<STATE> doubletonIj = mStatePair2Var.get(states[i], states[j]);
					final Doubleton<STATE> doubletonJk = mStatePair2Var.get(states[j], states[k]);
					final Doubleton<STATE> doubletonIk = mStatePair2Var.get(states[i], states[k]);

					addTransitivityClausesToSolver(doubletonIj, doubletonJk, doubletonIk);
				}
				checkTimeout(ADDING_TRANSITIVITY_CONSTRAINTS);
			}
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	protected Doubleton<STATE>[] getEmptyVariableArray() {
		return EMPTY_LITERALS;
	}

	@Override
	protected abstract boolean isInitialPair(final STATE state1, final STATE state2);

	@Override
	protected boolean isInitialPair(final Doubleton<STATE> pair) {
		return isInitialPair(pair.getOneElement(), pair.getOtherElement());
	}

	@Override
	protected IPartition<STATE> constructResultEquivalenceClasses() throws AssertionError {
		final UnionFind<STATE> resultingEquivalenceClasses = new UnionFind<>();
		for (final STATE state : mOperand.getStates()) {
			resultingEquivalenceClasses.makeEquivalenceClass(state);
		}
		if (mSolver instanceof DimacsMaxSatSolver && DimacsMaxSatSolver.ONLY_PRODUCE_OUTPUT_FILE) {
			// early termination, only produce output file
			return resultingEquivalenceClasses;
		}
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
			}
		}
		return resultingEquivalenceClasses;
	}

	@Override
	protected abstract AbstractMaxSatSolver<Doubleton<STATE>> createTransitivitySolver();
}
