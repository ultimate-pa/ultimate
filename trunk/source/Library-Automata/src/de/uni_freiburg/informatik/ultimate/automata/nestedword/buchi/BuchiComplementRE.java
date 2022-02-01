/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizeUnderappox;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementDeterministicStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Buchi complementation "<tt>RE</tt>".
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiComplementRE<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private INestedWordAutomaton<LETTER, STATE> mResult;

	private boolean mBuchiComplementReApplicable;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public <SF extends IDeterminizeStateFactory<STATE> & IBuchiComplementDeterministicStateFactory<STATE> & IBuchiIntersectStateFactory<STATE>> BuchiComplementRE(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataLibraryException {
		super(services);
		mOperand = operand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final INestedWordAutomaton<LETTER, STATE> operandWithoutNonLiveStates =
				(new ReachableStatesCopy<>(mServices, operand, false, false, false, true)).getResult();
		if (new IsDeterministic<>(mServices, operandWithoutNonLiveStates).getResult()) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Rüdigers determinization knack not necessary, already deterministic");
			}
			mResult = (new BuchiComplementDeterministic<>(mServices, stateFactory, operandWithoutNonLiveStates))
					.getResult();
		} else {
			final PowersetDeterminizer<LETTER, STATE> pd =
					new PowersetDeterminizer<>(operandWithoutNonLiveStates, true, stateFactory);
			final INestedWordAutomaton<LETTER, STATE> determinized =
					(new DeterminizeUnderappox<>(mServices, stateFactory, operandWithoutNonLiveStates, pd)).getResult();
			final INestedWordAutomaton<LETTER, STATE> determinizedComplement =
					(new BuchiComplementDeterministic<>(mServices, stateFactory, determinized)).getResult();
			final INestedWordAutomaton<LETTER, STATE> intersectionWithOperand = (new BuchiIntersectDD<>(mServices,
					stateFactory, operandWithoutNonLiveStates, determinizedComplement, true)).getResult();
			final NestedLassoRun<LETTER, STATE> run =
					(new BuchiIsEmpty<>(mServices, intersectionWithOperand)).getAcceptingNestedLassoRun();
			if (run == null) {
				if (mLogger.isInfoEnabled()) {
					mLogger.info("Rüdigers determinization knack applicable");
				}
				mBuchiComplementReApplicable = true;
				mResult = determinizedComplement;
			} else {
				if (mLogger.isInfoEnabled()) {
					mLogger.info("Rüdigers determinization knack not applicable");
				}
				mBuchiComplementReApplicable = false;
				mResult = null;
			}
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	/**
	 * @return true if buchiComplementRE was applicable on the input.
	 */
	public boolean applicable() {
		return mBuchiComplementReApplicable;
	}

	@Override
	public String exitMessage() {
		if (mBuchiComplementReApplicable) {
			return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
		}
		return "Unable to perform " + getOperationName() + "on this input";
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		if (mBuchiComplementReApplicable) {
			return mResult;
		}
		assert mResult == null;
		throw new UnsupportedOperationException("Operation was not applicable");
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return ResultChecker.buchiComplement(mServices, mOperand, mResult);
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}
}
