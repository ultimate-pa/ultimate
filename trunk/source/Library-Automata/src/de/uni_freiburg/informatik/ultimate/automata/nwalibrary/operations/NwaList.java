/*
 * Copyright (C) 2014-2015 Jeffery Hsu (a71128@gmail.com)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * Utility class that provides an interface for constructing a list of INestedWordAutomatons.  
 * @author jefferyyjhsu@iis.sinica.edu.tw
 */

public class NwaList<LETTER,STATE> implements IOperation<LETTER,STATE>{

	ArrayList<INestedWordAutomaton<LETTER,STATE>> automataCollection;
	private static ILogger m_Logger;
	
	public NwaList(AutomataLibraryServices services,INestedWordAutomaton<LETTER,STATE> orginalAutomata, INestedWordAutomaton<LETTER,STATE> newAutomata){
		m_Logger = services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Logger.info(startMessage());
		automataCollection = new ArrayList<INestedWordAutomaton<LETTER,STATE>>();
		automataCollection.add(orginalAutomata);
		automataCollection.add(newAutomata);
		m_Logger.info(exitMessage());
	}
	
	public NwaList(AutomataLibraryServices services,ArrayList<INestedWordAutomaton<LETTER,STATE>> orginalAutomataCollection, INestedWordAutomaton<LETTER,STATE> newAutomata){
		m_Logger = services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Logger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		m_Logger.info(exitMessage());
	}
	public NwaList(AutomataLibraryServices services,INestedWordAutomaton<LETTER,STATE> newAutomata,ArrayList<INestedWordAutomaton<LETTER,STATE>> orginalAutomataCollection){
		m_Logger = services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Logger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		m_Logger.info(exitMessage());
	}
	
	/**
	 * Constructs a list that consists of a single automaton.
	 */
	public NwaList(AutomataLibraryServices services,INestedWordAutomaton<LETTER,STATE> newAutomata){
		m_Logger = services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Logger.info(startMessage());
		automataCollection = new ArrayList<INestedWordAutomaton<LETTER,STATE>>();
		automataCollection.add(newAutomata);
		m_Logger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "NwaList";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName();
	}
	
	@Override
	public String exitMessage() {
		return "Exit " + operationName();
	}
	
	@Override
	public ArrayList<INestedWordAutomaton<LETTER,STATE>> getResult() throws AutomataLibraryException {
		return automataCollection;
	}
	/*public String getResult() throws OperationCanceledException {
		return "NwaList_result:"+automataCollection.size();
	}*/
	
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}
	
}
