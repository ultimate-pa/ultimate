/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Increase the number of accepting states without changing the language.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class BuchiClosure<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final INestedWordAutomaton<LETTER, STATE> mResult;
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 */
	public BuchiClosure(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
		mLogger.info(startMessage());
		mResult = new BuchiClosureNwa<LETTER, STATE>(mServices, mOperand);
		mLogger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "buchiClosure";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand "
				+ mOperand.sizeInformation() + " thereof "
				+ mOperand.getFinalStates().size() + " accepting";
	}
	
	@Override
	public String exitMessage() {
		return "Start " + operationName() + " Operand "
				+ mResult.sizeInformation() + " thereof "
				+ mResult.getFinalStates().size() + " accepting";
	}
	
	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean correct = true;
		mLogger.info("Start testing correctness of " + operationName());
		
		final List<NestedLassoWord<LETTER>> lassoWords =
				new ArrayList<NestedLassoWord<LETTER>>();
		final BuchiIsEmpty<LETTER, STATE> operandEmptiness =
				new BuchiIsEmpty<LETTER, STATE>(mServices, mOperand);
		final boolean operandEmpty = operandEmptiness.getResult();
		if (!operandEmpty) {
			lassoWords.add(operandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> resultEmptiness =
				new BuchiIsEmpty<LETTER, STATE>(mServices, mResult);
		final boolean resultEmpty = resultEmptiness.getResult();
		if (!resultEmpty) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		correct &= (operandEmpty == resultEmpty);
		assert correct;
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
}
