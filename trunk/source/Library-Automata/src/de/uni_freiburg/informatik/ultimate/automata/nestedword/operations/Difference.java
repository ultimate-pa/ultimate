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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Computes the difference of two nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class Difference<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE>
		implements IOpWithDelayedDeadEndRemoval<LETTER, STATE> {
	private final INestedWordAutomatonSimple<LETTER, STATE> mFstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSndOperand;
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	private IntersectNwa<LETTER, STATE> mIntersect;
	private NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	private DoubleDeckerAutomatonFilteredStates<LETTER, STATE> mResultWOdeadEnds;
	private final IStateFactory<STATE> mStateFactory;
	
	// TODO Christian 2016-09-04: These fields are only used locally. Is there some functionality missing?
	private DeterminizeNwa<LETTER, STATE> mSndDeterminized;
	private ComplementDeterministicNwa<LETTER, STATE> mSndComplemented;
	
	public Difference(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer, final boolean finalIsTrap)
			throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = stateFactory;
		mStateDeterminizer = stateDeterminizer;
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		
		// TODO Christian 2016-09-04: The parameter finalIsTrap is always 'false'.
		computeDifference(finalIsTrap);
		
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
	public Difference(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		this(services, stateFactory, fstOperand, sndOperand,
				new PowersetDeterminizer<>(sndOperand, true, stateFactory), false);
	}
	
	@Override
	public String operationName() {
		return "Difference";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + mResult.sizeInformation();
	}
	
	private void computeDifference(final boolean finalIsTrap) throws AutomataLibraryException {
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			final TotalizeNwa<LETTER, STATE> sndTotalized = new TotalizeNwa<>(mSndOperand, mStateFactory);
			final ComplementDeterministicNwa<LETTER, STATE> sndComplemented =
					new ComplementDeterministicNwa<>(sndTotalized);
			final IntersectNwa<LETTER, STATE> intersect =
					new IntersectNwa<>(mFstOperand, sndComplemented, mStateFactory, finalIsTrap);
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
		// computation of Hoare annotation in Trace Abstration is incorrect if automaton is not total
		final boolean makeAutomatonTotal = true;
		mSndDeterminized = new DeterminizeNwa<>(mServices, mSndOperand, mStateDeterminizer, mStateFactory, null,
				makeAutomatonTotal);
		mSndComplemented = new ComplementDeterministicNwa<>(mSndDeterminized);
		mIntersect = new IntersectNwa<>(mFstOperand, mSndComplemented, mStateFactory, finalIsTrap);
		mResult = new NestedWordAutomatonReachableStates<>(mServices, mIntersect);
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}
	
	@Override
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		if (mResultWOdeadEnds == null) {
			return mResult;
		}
		return mResultWOdeadEnds;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + operationName());
		}
		final INestedWordAutomatonSimple<LETTER, STATE> resultDd = (new DifferenceDD<>(mServices,
				mFstOperand, mSndOperand, new PowersetDeterminizer<>(mSndOperand, true, stateFactory),
				stateFactory, false, false)).getResult();
		boolean correct = true;
		/*
		correct &= (resultDd.size() == mResult.size());
		assert correct;
		*/
		correct &= new IsIncluded<>(mServices, stateFactory, resultDd, mResult).getResult();
		assert correct;
		correct &= new IsIncluded<>(mServices, stateFactory, mResult, resultDd).getResult();
		assert correct;
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, operationName() + "Failed",
					"language is different", mFstOperand, mSndOperand);
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + operationName());
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
