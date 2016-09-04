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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Operation that checks if the language of the first operand is included in the
 * language of the second automaton.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class IsIncluded<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE> {
	private final INestedWordAutomatonSimple<LETTER, STATE> mFstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSndOperand;
	private final Boolean mResult;
	private final NestedRun<LETTER, STATE> mCounterexample;
	
	/**
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param fstOperand first operand
	 * @param sndOperand second operand
	 * @throws AutomataLibraryException if construction fails
	 */
	public IsIncluded(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand)
					throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mLogger.info(startMessage());
		final IsEmpty<LETTER, STATE> emptinessCheck = new IsEmpty<LETTER, STATE>(
				services, (new Difference<LETTER, STATE>(
						mServices, stateFactory, fstOperand, sndOperand)).getResult());
		mResult = emptinessCheck.getResult();
		mCounterexample = emptinessCheck.getNestedRun();
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
		return mFstOperand;
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	public NestedRun<LETTER, STATE> getCounterexample() {
		return mCounterexample;
	}
}
