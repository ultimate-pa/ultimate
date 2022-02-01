/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;

/**
 * Totalizes a nested word automaton, i.e., makes every state have an outgoing transition for every letter.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class Totalize<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mResult;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory (used for automaton construction)
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public Totalize(final AutomataLibraryServices services, final ISinkStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final TotalizeNwa<LETTER, STATE> totalized = new TotalizeNwa<>(operand, stateFactory, false);
		mResult = new NestedWordAutomatonReachableStates<>(mServices, totalized);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Result " + mResult.sizeInformation();
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + getOperationName());
		}

		final String message;
		final boolean correct;

		// check language equivalence
		final IsEquivalent<LETTER, STATE> equivalenceCheck =
				new IsEquivalent<>(mServices, stateFactory, getOperand(), getResult());

		if (!equivalenceCheck.getResult()) {
			// language equivalence check failed
			message = equivalenceCheck.getViolationMessage();
			correct = false;
			assert false;
		} else if (!new IsTotal<>(mServices, mResult).getResult()) {
			// totality check failed
			message = "The result is not total.";
			correct = false;
			assert false;
		} else {
			message = null;
			correct = true;
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed", message, mOperand);
		}
		return correct;
	}
}
