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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsSemiDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Operation that checks if the language of the first Buchi automaton is included in the language of the second Buchi
 * automaton.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiIsIncluded<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;

	private final Boolean mResult;

	private final NestedLassoRun<LETTER, STATE> mCounterexample;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public BuchiIsIncluded(final AutomataLibraryServices services,
			final IBuchiNwaInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndComplement =
				(new BuchiComplementFKV<>(mServices, stateFactory, mSndOperand)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> difference =
				(new BuchiIntersectDD<>(mServices, stateFactory, mFstOperand, sndComplement, true)).getResult();
		final BuchiIsEmpty<LETTER, STATE> emptinessCheck = new BuchiIsEmpty<>(mServices, difference);

		mResult = emptinessCheck.getResult();
		mCounterexample = emptinessCheck.getAcceptingNestedLassoRun();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Language is " + (mResult ? "" : "not ") + "included";
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	public NestedLassoRun<LETTER, STATE> getCounterexample() {
		return mCounterexample;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
	
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics result = constructBasicInclusionStatistics(mServices, mLogger, this);

		return result;
	}

	static <LETTER, STATE> AutomataOperationStatistics constructBasicInclusionStatistics(final AutomataLibraryServices services,
			final ILogger logger, final BinaryNwaOperation<LETTER, STATE, ?> buchiIsIncludedOperation) {
		final AutomataOperationStatistics result = new AutomataOperationStatistics();
		final int lhsSize = buchiIsIncludedOperation.getFirstOperand().size();
		final int rhsSize = buchiIsIncludedOperation.getSecondOperand().size();
		Boolean rhsIsDeterministic = null;
		try {
			rhsIsDeterministic = new IsDeterministic<>(services, buchiIsIncludedOperation.getSecondOperand()).getResult();
		} catch (final AutomataOperationCanceledException e) {
			logger.info("wanted to run IsDeterministic for statistics but toolchain was cancelled");
		}
		Boolean rhsIsSemiDeterministic = null;
		try {
			rhsIsSemiDeterministic = new IsSemiDeterministic<>(services, buchiIsIncludedOperation.getSecondOperand()).getResult();
		} catch (final AutomataOperationCanceledException e) {
			logger.info("wanted to run IsSemiDeterministic for statistics but toolchain was cancelled");
		}

		final boolean isIncluded = (boolean) buchiIsIncludedOperation.getResult();

		result.addKeyValuePair(StatisticsType.STATES_LHS, lhsSize);
		result.addKeyValuePair(StatisticsType.STATES_RHS, rhsSize);
		result.addKeyValuePair(StatisticsType.RHS_IS_DETERMINISTIC, rhsIsDeterministic);
		result.addKeyValuePair(StatisticsType.RHS_IS_SEMIDETERMINISTIC, rhsIsSemiDeterministic);
		result.addKeyValuePair(StatisticsType.IS_INCLUDED, isIncluded);
		return result;
	}
}
