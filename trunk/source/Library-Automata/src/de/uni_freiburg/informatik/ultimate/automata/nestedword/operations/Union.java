/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;

/**
 * Computes the union of two nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class Union<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mResult;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public Union(final AutomataLibraryServices services, final IUnionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		
		final TotalizeNwa<LETTER, STATE> fstTotalized = new TotalizeNwa<>(mFstOperand, stateFactory, false);
		final TotalizeNwa<LETTER, STATE> sndTotalized = new TotalizeNwa<>(mSndOperand, stateFactory, false);
		final UnionNwa<LETTER, STATE> union = new UnionNwa<>(fstTotalized, sndTotalized, stateFactory, false);
		mResult = new NestedWordAutomatonReachableStates<>(mServices, union);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
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
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + getOperationName());
		}

		final IDoubleDeckerAutomaton<LETTER, STATE> resMinusFst =
				new Difference<>(mServices, stateFactory, mResult, mFstOperand).getResult();
		final IDoubleDeckerAutomaton<LETTER, STATE> resMinusSnd =
				new Difference<>(mServices, stateFactory, mResult, mSndOperand).getResult();
		boolean correct;
		correct = new IsIncluded<>(mServices, stateFactory, mSndOperand, resMinusFst).getResult();
		assert correct;
		correct = correct && new IsIncluded<>(mServices, stateFactory, mFstOperand, resMinusSnd).getResult();
		assert correct;
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
					"language is different", mFstOperand, mSndOperand);
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}
}
