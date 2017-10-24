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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations.difference;

import java.util.Collection;
import java.util.HashSet;

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
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Intersect;

/**
 * Computes the difference of two given bottom-up tree automata.<br>
 * <br>
 * This means that the resulting automaton accepts the language
 * {@code L(firstOperand) \ L(secondOperand)}.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <LETTER>
 *            The type of the ranked letters of the tree automata
 * @param <STATE>
 *            The type of the states of the tree automata
 */
public final class Difference<LETTER extends IRankedLetter, STATE>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> 
		implements IOperation<LETTER, STATE, IStateFactory<STATE>> {
	/**
	 * The first operand for the difference operation.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mFirstOperand;
	/**
	 * The resulting tree automaton after computing the difference.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mResult;
	/**
	 * The second operand for the difference operation.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mSecondOperand;

	/**
	 * Computes the difference of the two given tree automata.<br>
	 * <br>
	 * This means that the resulting automaton accepts the language
	 * {@code L(firstOperand) \ L(secondOperand)}.
	 * 
	 * @param <SF>
	 *            The type of the state factory to use for intermediate methods,
	 *            must provide methods for merging states, creating sink states
	 *            and intersecting states.
	 * @param services
	 *            Ultimate services
	 * @param factory
	 *            The state factory to use for intermediate methods.
	 * @param firstOperand
	 *            The first operand for the difference operation
	 * @param secondOperand
	 *            The second operand for the difference operation
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> Difference(
			final AutomataLibraryServices services, final SF factory,
			final ITreeAutomatonBU<LETTER, STATE> firstOperand, final ITreeAutomatonBU<LETTER, STATE> secondOperand)
					throws AutomataOperationCanceledException {
		super(services);

		this.mFirstOperand = firstOperand;
		this.mSecondOperand = secondOperand;

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(startMessage());
		}

		this.mResult = computeDifference(factory);

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(exitMessage());
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return this.mResult;
	}

	/**
	 * Computes and returns the difference of the two given tree automata.<br>
	 * <br>
	 * This means that the resulting automaton accepts the language
	 * {@code L(firstOperand) \ L(secondOperand)}. Therefore the current
	 * implementation sees the difference as the equivalent operation
	 * {@code intersect(first, complement(second))}. Thus it falls back to
	 * Operations {@link Complement} and {@link Intersect}.
	 * 
	 * @param <SF>
	 *            The type of the state factory to use for intermediate methods,
	 *            must provide methods for merging states, creating sink states
	 *            and intersecting states.
	 * @param factory
	 *            The state factory to use for intermediate methods
	 * @return The difference of the two given tree automata
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> ITreeAutomatonBU<LETTER, STATE> computeDifference(
			final SF factory) throws AutomataOperationCanceledException {
		// Difference can be seen as intersect(first, complement(second))
		// First compute complement(second)
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to compute complement(second).");
		}
		final Collection<LETTER> alphabet = new HashSet<>();
		alphabet.addAll(this.mFirstOperand.getAlphabet());
		alphabet.addAll(this.mSecondOperand.getAlphabet());

		final ITreeAutomatonBU<LETTER, STATE> secondOperandComplemented = new Complement<>(this.mServices, factory,
				this.mSecondOperand, alphabet).getResult();

		// If operation was canceled, for example from the
		// Ultimate framework
		if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
			this.mLogger.debug("Stopped after computing complement(second).");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		// Now compute the intersection which is also the final result
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to compute intersect(first, secondComplemented).");
		}
		return new Intersect<>(this.mServices, factory, this.mFirstOperand, secondOperandComplemented).getResult();
	}
	

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
