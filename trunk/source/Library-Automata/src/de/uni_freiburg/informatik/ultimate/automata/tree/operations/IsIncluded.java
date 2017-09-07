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

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;

/**
 * Computes if the language of a given bottom-up tree automaton is included in
 * the language of another tree automaton.<br>
 * <br>
 * This means that the result is <tt>true</tt> if the all accepted runs of the
 * first automaton are also accepted by the second automaton, else it is
 * <tt>false</tt>.<br>
 * <br>
 * If the inclusion does not hold then {@link #getCounterexample()} offers such
 * a tree run that is not accepted by the second automaton while accepted by the
 * first.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <LETTER>
 *            The type of the ranked letters of the tree automata
 * @param <STATE>
 *            The type of the states of the tree automata
 */
public final class IsIncluded<LETTER extends IRankedLetter, STATE>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>>
		implements IOperation<LETTER, STATE, IStateFactory<STATE>> {
	/**
	 * If the inclusion does not hold then this field holds a tree run that acts as
	 * counterexample to the inclusion. This means it represents a run that is
	 * accepted by the first operand but not by the second operand.
	 */
	private final TreeRun<LETTER, STATE> mCounterexample;
	/**
	 * The result of the inclusion check, <tt>true</tt> if the language of the first
	 * operand is included in the language of the second operand, <tt>false</tt>
	 * otherwise.
	 */
	private final Boolean mResult;

	/**
	 * Computes if the language of a given bottom-up tree automaton is included in
	 * the language of another tree automaton.<br>
	 * <br>
	 * This means that the result is <tt>true</tt> if the all accepted runs of the
	 * first automaton are also accepted by the second automaton, else it is
	 * <tt>false</tt>.<br>
	 * <br>
	 * If the inclusion does not hold then {@link #getCounterexample()} offers such
	 * a tree run that is not accepted by the second automaton while accepted by the
	 * first.
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
	 *            The first operand for the inclusion check
	 * @param secondOperand
	 *            The second operand for the inclusion check
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> IsIncluded(
			final AutomataLibraryServices services, final SF factory,
			final ITreeAutomatonBU<LETTER, STATE> firstOperand, final ITreeAutomatonBU<LETTER, STATE> secondOperand)
			throws AutomataOperationCanceledException {
		super(services);

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(startMessage());
		}

		// Inclusion can be seen as isEmpty(difference(first, second))
		// First compute the difference
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to compute difference(first, second).");
		}
		final ITreeAutomatonBU<LETTER, STATE> difference = new Difference<>(services, factory, firstOperand,
				secondOperand).getResult();

		// If operation was canceled, for example from the
		// Ultimate framework
		if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
			this.mLogger.debug("Stopped after difference(first, second).");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		// Check whether it is empty
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to compute isEmpty(difference).");
		}
		final IsEmpty<LETTER, STATE> emptinessCheck = new IsEmpty<>(services, difference);

		this.mResult = emptinessCheck.getResult();
		this.mCounterexample = emptinessCheck.getTreeRun();

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
		return "Finished " + getOperationName() + ". Language is " + (this.mResult.booleanValue() ? "" : "not ")
				+ "included";
	}

	/**
	 * If the inclusion check does not hold then this method offers a tree run that
	 * acts as counterexample. This means that this tree run is accepted by the
	 * first automaton while not by the second. If the inclusion check holds than
	 * this method does not provide such a tree run.
	 * 
	 * @return A tree run that acts as counterexample for the inclusion, if present
	 */
	public Optional<TreeRun<LETTER, STATE>> getCounterexample() {
		// If the inclusion holds then there is no counterexample
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

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

}
