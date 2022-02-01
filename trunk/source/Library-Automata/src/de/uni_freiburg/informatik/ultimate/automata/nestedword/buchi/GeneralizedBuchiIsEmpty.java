/*
 * Copyright (C) 2017      Yong Li  (liyong@ios.ac.cn)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * Copyright (C) 2010-2015 wuxio
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
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.AbstractGeneralizedAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.GeneralizedNestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.GeneralizedNestedWordAutomatonReachableStatesAntichain;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Class that provides the Buchi emptiness check for nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Yong Li
 * @version 2010-12-18
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels (the content) of the automata states.
 */
public final class GeneralizedBuchiIsEmpty<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> mReach;
	private final Boolean mResult;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public GeneralizedBuchiIsEmpty(final AutomataLibraryServices services, final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		try {
			if (mOperand instanceof GeneralizedNestedWordAutomatonReachableStates
			|| mOperand instanceof GeneralizedNestedWordAutomatonReachableStatesAntichain) {
				mReach = (AbstractGeneralizedAutomatonReachableStates<LETTER, STATE>) mOperand;
			} else{
				mReach = new GeneralizedNestedWordAutomatonReachableStates<>(mServices, mOperand);
			}
			mResult = mReach.isEmpty();
		} catch (final AutomataOperationCanceledException oce) {
			throw new AutomataOperationCanceledException(getClass());
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Result is " + mResult;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	/**
	 * @return An accepting nested lasso run.
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public NestedLassoRun<LETTER, STATE> getAcceptingNestedLassoRun() throws AutomataOperationCanceledException {
		if (mResult) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("There is no accepting nested lasso run");
			}
			return null;
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Starting construction of run");
		}
		return mReach.getNestedLassoRun();
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
