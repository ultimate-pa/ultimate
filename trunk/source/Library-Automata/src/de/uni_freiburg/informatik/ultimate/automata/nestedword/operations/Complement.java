/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;

/**
 * Complements a nested word automaton.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class Complement<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private ComplementDeterministicNwa<LETTER, STATE> mComplement;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	private final ISinkStateFactory<STATE> mStateFactory;

	/**
	 * Constructor with default values.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public <SF extends ISinkStateFactory<STATE> & IDeterminizeStateFactory<STATE>> Complement(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, new PowersetDeterminizer<>(operand, true, stateFactory));
	}

	/**
	 * Extended constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @param stateDeterminizer
	 *            state determinizer
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public Complement(final AutomataLibraryServices services, final ISinkStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mStateDeterminizer = stateDeterminizer;
		mStateFactory = stateFactory;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = computeComplement();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private NestedWordAutomatonReachableStates<LETTER, STATE> computeComplement()
			throws AutomataOperationCanceledException {
		DeterminizeNwa<LETTER, STATE> determinized;
		if (mOperand instanceof DeterminizeNwa) {
			determinized = (DeterminizeNwa<LETTER, STATE>) mOperand;
			mComplement = new ComplementDeterministicNwa<>(determinized);
			return new NestedWordAutomatonReachableStates<>(mServices, mComplement);
		}
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			final NestedWordAutomatonReachableStates<LETTER, STATE> result = tryWithoutDeterminization();
			if (result != null) {
				return result;
			}
		}
		determinized = new DeterminizeNwa<>(mServices, mOperand, mStateDeterminizer, mStateFactory, null, true);
		mComplement = new ComplementDeterministicNwa<>(determinized);
		return new NestedWordAutomatonReachableStates<>(mServices, mComplement);
	}

	private NestedWordAutomatonReachableStates<LETTER, STATE> tryWithoutDeterminization()
			throws AutomataOperationCanceledException {
		assert mStateDeterminizer instanceof PowersetDeterminizer;
		final TotalizeNwa<LETTER, STATE> totalized = new TotalizeNwa<>(mOperand, mStateFactory, true);
		final ComplementDeterministicNwa<LETTER, STATE> complemented = new ComplementDeterministicNwa<>(totalized);
		final NestedWordAutomatonReachableStates<LETTER, STATE> result =
				new NestedWordAutomatonReachableStates<>(mServices, complemented);
		if (!totalized.nonDeterminismInInputDetected()) {
			mComplement = complemented;
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Operand was deterministic. Have not used determinization.");
			}
			return result;
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Operand was not deterministic. Recomputing result with determinization.");
		}
		return null;
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
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
		boolean correct = true;
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Start testing correctness of " + getOperationName());
			}
			// intersection of operand and result should be empty
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> intersectionOperandResult =
					(new IntersectDD<>(mServices, stateFactory, mOperand, mResult)).getResult();
			correct &= (new IsEmpty<>(mServices, intersectionOperandResult)).getResult();
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> resultDd =
					(new ComplementDD<>(mServices, stateFactory, mOperand)).getResult();

			// should have same number of states as old complementation
			// does not hold, resultDD sometimes has additional sink state
			//		correct &= (resultDD.size() == mResult.size());

			// should recognize same language as old computation
			correct &= new IsEquivalent<>(mServices, stateFactory, resultDd, mResult).getResult();

			if (mLogger.isInfoEnabled()) {
				mLogger.info("Finished testing correctness of " + getOperationName());
			}
		} else {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("operation not tested");
			}
		}
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
					"language is different", mOperand);
		}
		return correct;
	}
}
