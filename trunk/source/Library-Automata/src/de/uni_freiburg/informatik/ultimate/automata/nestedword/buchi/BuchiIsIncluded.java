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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Operation that checks if the language of the first Buchi automaton is
 * included in the language of the second Buchi automaton.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class BuchiIsIncluded<LETTER, STATE> extends BinaryNwaOperation<LETTER,STATE> {

	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand1;
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand2;

	private final Boolean mResult;

	private final NestedLassoRun<LETTER, STATE> mCounterexample;

	public BuchiIsIncluded(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa1,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa2)
			throws AutomataLibraryException {
		super(services);
		mOperand1 = nwa1;
		mOperand2 = nwa2;
		mLogger.info(startMessage());

		final INestedWordAutomaton<LETTER, STATE> sndComplement = (new BuchiComplementFKV<LETTER, STATE>(
				mServices, stateFactory, mOperand2)).getResult();
		final INestedWordAutomaton<LETTER, STATE> difference = (new BuchiIntersectDD<LETTER, STATE>(
				mServices, mOperand1, sndComplement, true)).getResult();
		final BuchiIsEmpty<LETTER, STATE> emptinessCheck = new BuchiIsEmpty<LETTER, STATE>(
				mServices, difference);

		mResult = emptinessCheck.getResult();
		mCounterexample = emptinessCheck.getAcceptingNestedLassoRun();
		mLogger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "isIncluded";
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Language is "
				+ (mResult ? "" : "not ") + "included";
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getFirstOperand() {
		return mOperand1;
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getSecondOperand() {
		return mOperand2;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	public NestedLassoRun<LETTER, STATE> getCounterexample() {
		return mCounterexample;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}

}
