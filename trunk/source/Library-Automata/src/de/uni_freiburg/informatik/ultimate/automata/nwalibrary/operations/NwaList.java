package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * Utility class that provides an interface for constructing a list of INestedWordAutomatons.  
 * @author jefferyyjhsu@iis.sinica.edu.tw
 */

public class NwaList<LETTER,STATE> implements IOperation<LETTER,STATE>{

	ArrayList<INestedWordAutomaton<LETTER,STATE>> automataCollection;
	private static Logger m_Logger;
	
	public NwaList(IUltimateServiceProvider services,INestedWordAutomaton<LETTER,STATE> orginalAutomata, INestedWordAutomaton<LETTER,STATE> newAutomata){
		m_Logger = services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Logger.info(startMessage());
		automataCollection = new ArrayList<INestedWordAutomaton<LETTER,STATE>>();
		automataCollection.add(orginalAutomata);
		automataCollection.add(newAutomata);
		m_Logger.info(exitMessage());
	}
	
	public NwaList(IUltimateServiceProvider services,ArrayList<INestedWordAutomaton<LETTER,STATE>> orginalAutomataCollection, INestedWordAutomaton<LETTER,STATE> newAutomata){
		m_Logger = services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Logger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		m_Logger.info(exitMessage());
	}
	public NwaList(IUltimateServiceProvider services,INestedWordAutomaton<LETTER,STATE> newAutomata,ArrayList<INestedWordAutomaton<LETTER,STATE>> orginalAutomataCollection){
		m_Logger = services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Logger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		m_Logger.info(exitMessage());
	}
	
	/**
	 * Constructs a list that consists of a single automaton.
	 */
	public NwaList(IUltimateServiceProvider services,INestedWordAutomaton<LETTER,STATE> newAutomata){
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
