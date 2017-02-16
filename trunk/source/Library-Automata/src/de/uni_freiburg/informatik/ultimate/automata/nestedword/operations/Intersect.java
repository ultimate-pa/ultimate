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
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Computes the intersection of two nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class Intersect<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE> {
	private final INestedWordAutomatonSimple<LETTER, STATE> mFstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSndOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	
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
	public Intersect(final AutomataLibraryServices services, final IIntersectionStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		
		final IntersectNwa<LETTER, STATE> intersect = new IntersectNwa<>(mFstOperand, mSndOperand, stateFactory, false);
		mResult = new NestedWordAutomatonReachableStates<>(mServices, intersect);
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}
	
	@Override
	public String operationName() {
		return "Intersect";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Result " + mResult.sizeInformation();
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
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + operationName());
		}
		
		// TODO Christian 2017-02-15 Temporary workaround until state factory becomes class parameter
		final INestedWordAutomatonSimple<LETTER, STATE> resultDd = (new IntersectDD<>(mServices,
				(IBuchiIntersectStateFactory<STATE> & IIntersectionStateFactory<STATE>) stateFactory, mFstOperand,
				mSndOperand)).getResult();
		boolean correct = true;
		correct &= (resultDd.size() == mResult.size());
		assert correct;
		correct &= new IsEquivalent<>(mServices,
				(ISinkStateFactory<STATE> & IDeterminizeStateFactory<STATE> & IIntersectionStateFactory<STATE>) stateFactory,
				resultDd, mResult).getResult();
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
}
