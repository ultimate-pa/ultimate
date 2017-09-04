/*
 * Copyright (C) 2014-2017 Daniel Tischner <zabuza.dev@gmail.com>
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;

/**
 * Computes if the languages of two given bottom-up tree automata are
 * equivalent.<br>
 * <br>
 * This means that the result is <tt>true</tt> if all accepted runs of the of
 * one automaton are also accepted by the other automaton and vice versa, else
 * it is <tt>false</tt>.<br>
 * <br>
 * If the equivalence does not hold then {@link #getCounterexample()} offers
 * such a tree run that is not accepted by one automaton while accepted by the
 * other.
 *
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <LETTER>
 *            The type of the ranked letters of the tree automata
 * @param <STATE>
 *            The type of the states of the tree automata
 */
public final class IsEquivalent<LETTER extends IRankedLetter, STATE>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {
	/**
	 * Demo usage of the equivalence check. Also used for debugging purpose.
	 *
	 * @param args
	 *            Not supported
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public static void main(final String[] args) throws AutomataOperationCanceledException {
		// Dummy services
		final AutomataLibraryServices services = new AutomataLibraryServices(new ToolchainStorage());
		final StringFactory factory = new StringFactory();

		// Arguments for generation of a random tree automaton
		final int numberOfStates = 4;
		final int[] rankToNumberOfLetters = { 2, 0, 1, 2 };
		final int[] rankToNumberOfTransitionsPerLetter = { 2, 0, 5, 5 };
		final double acceptanceDensity = 0.2;

		final GetRandomDftaBU getRandomTree = new GetRandomDftaBU(services, numberOfStates, rankToNumberOfLetters,
				rankToNumberOfTransitionsPerLetter, acceptanceDensity);
		final ITreeAutomatonBU<StringRankedLetter, String> firstTree = getRandomTree.getResult();

		final ITreeAutomatonBU<StringRankedLetter, String> secondTree = new Minimize<>(services, factory, firstTree)
				.getResult();
		final IsEquivalent<StringRankedLetter, String> isEquivalent = new IsEquivalent<>(services, factory, firstTree,
				secondTree);
		
		if (isEquivalent.getResult().booleanValue()) {
			System.out.println("Is equivalent.");
		} else {
			System.out.println("Is not equivalent, counterexample:");
			System.out.println(isEquivalent.getCounterexample().get());
		}
	}

	/**
	 * If the equivalence does not hold then this field holds a tree run that acts
	 * as counterexample to the equivalence. This means it represents a run that is
	 * accepted by one of the operands but not by the other.
	 */
	private TreeRun<LETTER, STATE> mCounterexample;
	/**
	 * The message used for logging purpose at exiting this operation.
	 */
	private String mExitMessage;
	/**
	 * The first operand for the equivalence check.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mFirstOperand;
	/**
	 * The result of the equivalence check, <tt>true</tt> if the languages of both
	 * operands are equivalent, <tt>false</tt> otherwise.
	 */
	private final Boolean mResult;

	/**
	 * The second operand for the equivalence check.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mSecondOperand;

	/**
	 * Computes if the languages of two given bottom-up tree automata are
	 * equivalent.<br>
	 * <br>
	 * This means that the result is <tt>true</tt> if all accepted runs of the of
	 * one automaton are also accepted by the other automaton and vice versa, else
	 * it is <tt>false</tt>.<br>
	 * <br>
	 * If the equivalence does not hold then {@link #getCounterexample()} offers
	 * such a tree run that is not accepted by one automaton while accepted by the
	 * other.
	 *
	 * @param <SF>
	 *            The type of the state factory to use for intermediate methods,
	 *            must provide methods for merging states, creating sink states and
	 *            intersecting states.
	 * @param services
	 *            Ultimate services
	 * @param factory
	 *            The state factory to use for intermediate methods.
	 * @param firstOperand
	 *            The first operand for the equivalence check
	 * @param secondOperand
	 *            The second operand for the equivalence check
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> IsEquivalent(
			final AutomataLibraryServices services, final SF factory,
			final ITreeAutomatonBU<LETTER, STATE> firstOperand, final ITreeAutomatonBU<LETTER, STATE> secondOperand)
			throws AutomataOperationCanceledException {
		super(services);

		this.mFirstOperand = firstOperand;
		this.mSecondOperand = secondOperand;

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(startMessage());
		}

		this.mResult = Boolean.valueOf(checkEquivalence(factory));

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(exitMessage());
		}
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#exitMessage()
	 */
	@Override
	public String exitMessage() {
		return this.mExitMessage;
	}

	/**
	 * If the equivalence check does not hold then this method offers a tree run
	 * that acts as counterexample. This means that this tree run is accepted by one
	 * of the two automata while not by the other. If the equivalence check holds
	 * than this method does not provide such a tree run.
	 *
	 * @return A tree run that acts as counterexample for the equivalence, if
	 *         present
	 */
	public Optional<TreeRun<LETTER, STATE>> getCounterexample() {
		// If the equivalence holds then there is no counterexample
		if (this.mResult.booleanValue()) {
			return Optional.empty();
		}

		return Optional.of(this.mCounterexample);
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public Boolean getResult() {
		return this.mResult;
	}

	/**
	 * Checks if the two given tree automata are equivalent. Therefore inclusion in
	 * both direction is computed. If the equivalence does not hold then
	 * {@link #getCounterexample()} offers such a tree run that is not accepted by
	 * one automaton while accepted by the other.
	 *
	 * @param <SF>
	 *            The type of the state factory to use for intermediate methods,
	 *            must provide methods for merging states, creating sink states and
	 *            intersecting states.
	 * @param factory
	 *            The state factory to use for intermediate methods.
	 * @return <tt>True</tt> if both automata are equivalent, <tt>false</tt>
	 *         otherwise
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> boolean checkEquivalence(
			final SF factory) throws AutomataOperationCanceledException {
		// Equivalence can be seen language inclusion in both directions
		// First compute the isIncluded(first, second)
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to compute isIncluded(first, second).");
		}
		if (!checkInclusion(factory, this.mFirstOperand, this.mSecondOperand)) {
			this.mExitMessage = "The first operand recognizes a word not recognized by the second one.";
			return false;
		}

		// If operation was canceled, for example from the
		// Ultimate framework
		if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
			this.mLogger.debug("Stopped after isIncluded(first, second).");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		// Next compute the isIncluded(second, first)
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to compute isIncluded(second, first).");
		}
		if (!checkInclusion(factory, this.mSecondOperand, this.mFirstOperand)) {
			this.mExitMessage = "The second operand recognizes a word not recognized by the first one.";
			return false;
		}
		return true;
	}

	/**
	 * Checks language inclusion in one direction, whether the language of the first
	 * operand is included in the language of the second operand. If not then it
	 * also sets a counterexample to the internal fields.
	 *
	 * @param <SF>
	 *            The type of the state factory to use for intermediate methods,
	 *            must provide methods for merging states, creating sink states and
	 *            intersecting states.
	 * @param factory
	 *            The state factory to use for intermediate methods.
	 * @param firstOperand
	 *            The first operand for the inclusion check
	 * @param secondOperand
	 *            The second operand for the inclusion check
	 * @return <tt>True</tt> if the language of the first automaton is included in
	 *         the language of the second automaton, <tt>false</tt> otherwise
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> boolean checkInclusion(
			final SF factory, final ITreeAutomatonBU<LETTER, STATE> firstOperand,
			final ITreeAutomatonBU<LETTER, STATE> secondOperand) throws AutomataOperationCanceledException {
		final IsIncluded<LETTER, STATE> isIncluded = new IsIncluded<>(this.mServices, factory, firstOperand,
				secondOperand);
		if (!isIncluded.getResult().booleanValue()) {
			this.mCounterexample = isIncluded.getCounterexample().get();
			return false;
		}

		return true;
	}

}
