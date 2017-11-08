/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.GeneralizedBuchiIntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ComplementDeterministicNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.DeterminizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class GeneralizedDifference<LETTER, STATE>
		extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	private final ISinkStateFactory<STATE> mStateFactory;
	private ComplementDeterministicNwa<LETTER, STATE> mSndComplemented;
	protected AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> mResult;
	private GeneralizedBuchiIntersectNwa<LETTER, STATE> mIntersect; 
	
	public <SF extends ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> GeneralizedDifference(
			final AutomataLibraryServices services, final SF stateFactory,
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer) throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateDeterminizer = stateDeterminizer;
		mStateFactory = stateFactory;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		computeDifference(stateFactory);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private <SF extends IIntersectionStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> void computeDifference(
			final SF stateFactory) throws AutomataLibraryException {
		
		if (hasSeveralInitialStates(mSndOperand)) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Subtrahend was not deterministic. Computing result with determinization.");
			}
		} else if (mStateDeterminizer instanceof PowersetDeterminizer) {
			final TotalizeNwa<LETTER, STATE> sndTotalized = new TotalizeNwa<>(mSndOperand, mStateFactory, true);

			mSndComplemented = new ComplementDeterministicNwa<>(sndTotalized);
		    mIntersect = new GeneralizedBuchiIntersectNwa<>(mFstOperand, mSndComplemented, stateFactory);
			mResult = new GeneralizedNestedWordAutomatonReachableStates<>(mServices, mIntersect);
			if (!sndTotalized.nonDeterminismInInputDetected()) {
				if (mLogger.isInfoEnabled()) {
					mLogger.info("Subtrahend was deterministic. Have not used determinization.");
				}
				return;
			}
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Subtrahend was not deterministic. Recomputing result with determinization.");
			}
		}
		// computation of Hoare annotation in Trace Abstraction is incorrect if
		// automaton is not total
		final boolean makeAutomatonTotal = true;
		DeterminizeNwa<LETTER, STATE> sndDeterminized = new DeterminizeNwa<>(mServices, mSndOperand, mStateDeterminizer, mStateFactory, null,
				makeAutomatonTotal);
		mSndComplemented = new ComplementDeterministicNwa<>(sndDeterminized);
	    mIntersect = new GeneralizedBuchiIntersectNwa<>(mFstOperand, mSndComplemented, stateFactory);
		mResult = new GeneralizedNestedWordAutomatonReachableStates<>(mServices, mIntersect);
	}
	
	private boolean hasSeveralInitialStates(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton) {
		final Iterator<STATE> iterator = automaton.getInitialStates().iterator();
		if (!iterator.hasNext()) {
			// No initial state. E.g., the empty automaton does not have an initial state.
			return false;
		} else {
			iterator.next();
			return iterator.hasNext();
		}
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}
	
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSecondComplemented() {
		return mSndComplemented;
	} 

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

}
