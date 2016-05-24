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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Operation that checks if the language of the first operand is included in the
 * language of the second automaton.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class IsIncluded<LETTER, STATE> implements IOperation<LETTER,STATE> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand1;
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand2;
	
	private final Boolean mResult;
	private final NestedRun<LETTER, STATE> mCounterexample;
	
	
	public IsIncluded(AutomataLibraryServices services,
			StateFactory<STATE> stateFactory,
			INestedWordAutomatonSimple<LETTER, STATE> nwa1, 
			INestedWordAutomatonSimple<LETTER, STATE> nwa2) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand1 = nwa1;
		mOperand2 = nwa2;
		mLogger.info(startMessage());
		IsEmpty<LETTER, STATE> emptinessCheck = new IsEmpty<LETTER, STATE>(
				services, (new Difference<LETTER, STATE>(mServices, stateFactory, nwa1, nwa2)).getResult());
		mResult = emptinessCheck.getResult();
		mCounterexample = emptinessCheck.getNestedRun();
		mLogger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "isIncluded";
	}

	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Operand1 " + 
					mOperand1.sizeInformation() + ". Operand2 " + 
					mOperand2.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Language is " 
				+ (mResult ? "" : "not ") + "included";
	}

	@Override
	public Boolean getResult() throws AutomataLibraryException {
		return mResult;
	}

	public NestedRun<LETTER, STATE> getCounterexample() {
		return mCounterexample;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}
	


}
