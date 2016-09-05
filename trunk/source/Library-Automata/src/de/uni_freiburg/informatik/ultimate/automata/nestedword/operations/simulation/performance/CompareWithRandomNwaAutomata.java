/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.GetRandomNwa;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;

/**
 * Operation that compares the different types of nwa simulation methods for nwa
 * reduction using random automata.<br/>
 * The resulting automaton is the input automaton.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of nwa automaton, not used
 * @param <STATE>
 *            State class of nwa automaton, not used
 */
public final class CompareWithRandomNwaAutomata<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {

	/**
	 * The inputed nwa automaton.
	 */
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	/**
	 * The resulting nwa automaton.
	 */
	private final INestedWordAutomaton<LETTER, STATE> mResult;

	/**
	 * Compares the different types of nwa simulation methods for nwa reduction
	 * using random automata. Resulting automaton is the input automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            A nwa, it is not used by the operation
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public CompareWithRandomNwaAutomata(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mResult = operand;
		mLogger.info(startMessage());

		// Use operation with random automata
		final IStateFactory<String> snf = new StringFactory();

		final int n = 10;
		final int k = 3;
		final int acceptanceInPerc = 100;
		final int totalityInternalInPerc = 5;
		final int totalityCallInPerc = 2;
		final int totalityReturnInPerc = 1;
		final int logEvery = 50;
		final int amount = 1000;
		INestedWordAutomaton<String, String> nwa;

		for (int i = 1; i <= amount; i++) {
			if (i % logEvery == 0) {
				mLogger.info("Worked " + i + " automata");
			}

			nwa = new GetRandomNwa(services, k, n, (totalityInternalInPerc + 0.0f) / 100,
					(totalityCallInPerc + 0.0f) / 100, (totalityReturnInPerc + 0.0f) / 100,
					(acceptanceInPerc + 0.0f) / 100).getResult();
			try {
				new CompareReduceNwaSimulation<String, String>(services, snf, nwa);
			} catch (final AutomataOperationCanceledException e) {
				e.printStackTrace();
			}
		}
		mLogger.info(exitMessage());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#checkResult(
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory)
	 */
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public Object getResult() {
		return mResult;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#operationName()
	 */
	@Override
	public String operationName() {
		return "compareWithRandomNwaAutomata";
	}
}
