/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * Büchi complementation based on the method of Sistla, Vardi, Wolper: <br>
 * 
 *     “The Complementation Problem for Büchi Automata with Applications to
 *      Temporal Logic” (Elsevier, 1987) <br>
 *      
 * The actual implementation of this complementation method is located in the
 * class {@code BuchiComplementAutomatonSVW}.
 * 
 * @author Fabian Reiter
 *
 */
public class BuchiComplementSVW<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private INestedWordAutomatonOldApi<LETTER,STATE> m_Operand;
	private BuchiComplementAutomatonSVW<LETTER,STATE> m_Result;

	
	@Override
	public String operationName() {
		return "buchiComplementSVW";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand " +
				m_Operand.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Result " + 
				m_Result.sizeInformation();
	}
		
	public BuchiComplementSVW(INestedWordAutomatonOldApi<LETTER,STATE> operand)
			throws OperationCanceledException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		m_Result = new BuchiComplementAutomatonSVW<LETTER, STATE>(operand);
		s_Logger.info(exitMessage());
	}

	@Override
	public INestedWordAutomatonOldApi<LETTER,STATE> getResult()
			throws OperationCanceledException {
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return ResultChecker.buchiComplement(m_Operand, m_Result);
	}
	
}