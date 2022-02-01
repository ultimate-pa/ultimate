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

import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;

/**
 * Computes the difference of two nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class Difference<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>>
		implements IOpWithDelayedDeadEndRemoval<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	private IntersectNwa<LETTER, STATE> mIntersect;
	private NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	private DoubleDeckerAutomatonFilteredStates<LETTER, STATE> mResultWOdeadEnds;
	private final ISinkStateFactory<STATE> mStateFactory;
	private final IIntersectionStateFactory<STATE> mStateFactoryIntersection;

	// TODO Christian 2016-09-04: These fields are only used locally. Is there some functionality missing?
	private DeterminizeNwa<LETTER, STATE> mSndDeterminized;
	private ComplementDeterministicNwa<LETTER, STATE> mSndComplemented;

	public <SF extends ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE> & IEmptyStackStateFactory<STATE>> Difference(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer, final boolean finalIsTrap)
			throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = stateFactory;
		mStateFactoryIntersection = stateFactory;
		mStateDeterminizer = stateDeterminizer;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		computeDifference(stateFactory, finalIsTrap);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	/**
	 * Uses a PowersetDeterminizer.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory for powerset determinizer and intersection
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public Difference(final AutomataLibraryServices services, final INwaInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		this(services, stateFactory, fstOperand, sndOperand, new PowersetDeterminizer<>(sndOperand, true, stateFactory),
				false);
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Result " + mResult.sizeInformation();
	}

	private <SF extends IIntersectionStateFactory<STATE> & IEmptyStackStateFactory<STATE>> void
			computeDifference(final SF stateFactory, final boolean finalIsTrap) throws AutomataLibraryException {
		if (hasSeveralInitialStates(mSndOperand)) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Subtrahend was not deterministic. Computing result with determinization.");
			}
		} else if (mStateDeterminizer instanceof PowersetDeterminizer) {
			final TotalizeNwa<LETTER, STATE> sndTotalized = new TotalizeNwa<>(mSndOperand, mStateFactory, true);
			
			final ComplementDeterministicNwa<LETTER, STATE> sndComplemented =
					new ComplementDeterministicNwa<>(sndTotalized);
			final IntersectNwa<LETTER, STATE> intersect =
					new IntersectNwa<>(mFstOperand, sndComplemented, stateFactory, finalIsTrap);
			final NestedWordAutomatonReachableStates<LETTER, STATE> result =
					new NestedWordAutomatonReachableStates<>(mServices, intersect);
			if (!sndTotalized.nonDeterminismInInputDetected()) {
				mSndComplemented = sndComplemented;
				mIntersect = intersect;
				mResult = result;

				if (mLogger.isInfoEnabled()) {
					mLogger.info("Subtrahend was deterministic. Have not used determinization.");
				}
				return;
			}
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Subtrahend was not deterministic. Recomputing result with determinization.");
			}
		}
		// computation of Hoare annotation in Trace Abstraction is incorrect if automaton is not total
		final boolean makeAutomatonTotal = true;
		mSndDeterminized = new DeterminizeNwa<>(mServices, mSndOperand, mStateDeterminizer, mStateFactory, null,
				makeAutomatonTotal);
		mSndComplemented = new ComplementDeterministicNwa<>(mSndDeterminized);
		mIntersect = new IntersectNwa<>(mFstOperand, mSndComplemented, stateFactory, finalIsTrap);
		mResult = new NestedWordAutomatonReachableStates<>(mServices, mIntersect);
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
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		if (mResultWOdeadEnds == null) {
			return mResult;
		}
		return mResultWOdeadEnds;
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + getOperationName());
		}
		final INestedWordAutomaton<LETTER, STATE> fstUnreach = new RemoveUnreachable<>(mServices, mFstOperand).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> resultDd =
				(new DifferenceDD<>(mServices, stateFactory, fstUnreach, mSndOperand,
						new PowersetDeterminizer<>(mSndOperand, true, stateFactory), false, false)).getResult();
		boolean correct = true;
		/*
		correct &= (resultDd.size() == mResult.size());
		assert correct;
		*/
		correct &= new IsEquivalent<>(mServices, stateFactory, resultDd, mResult).getResult();
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

	@Override
	public boolean removeDeadEnds() throws AutomataOperationCanceledException {
		mResult.computeDeadEnds();
		mResultWOdeadEnds = new DoubleDeckerAutomatonFilteredStates<>(mServices, mResult, mResult.getWithOutDeadEnds());
		if (mLogger.isInfoEnabled()) {
			mLogger.info("With dead ends: " + mResult.getStates().size());
			mLogger.info("Without dead ends: " + mResultWOdeadEnds.getStates().size());
		}
		return mResult.getStates().size() != mResultWOdeadEnds.getStates().size();
	}

	@Override
	public long getDeadEndRemovalTime() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
		return mResult.getWithOutDeadEnds().getRemovedUpDownEntry();
	}

	public Map<STATE, Map<STATE, IntersectNwa<LETTER, STATE>.ProductState>> getFst2snd2res() {
		return mIntersect.getFst2snd2res();
	}
}
