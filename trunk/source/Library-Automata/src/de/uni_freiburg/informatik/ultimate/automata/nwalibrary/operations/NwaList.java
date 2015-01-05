package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * Utility class that provides an interface for constructing a list of INestedWordAutomatons.  
 * @author jefferyyjhsu@iis.sinica.edu.tw
 */

public class NwaList<LETTER,STATE> implements IOperation<LETTER,STATE>{

	ArrayList<INestedWordAutomaton<LETTER,STATE>> automataCollection;
	private static Logger s_Logger;
	
	public NwaList(IUltimateServiceProvider services,INestedWordAutomaton<LETTER,STATE> orginalAutomata, INestedWordAutomaton<LETTER,STATE> newAutomata){
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		automataCollection = new ArrayList<INestedWordAutomaton<LETTER,STATE>>();
		automataCollection.add(orginalAutomata);
		automataCollection.add(newAutomata);
		s_Logger.info(exitMessage());
	}
	
	public NwaList(IUltimateServiceProvider services,ArrayList<INestedWordAutomaton<LETTER,STATE>> orginalAutomataCollection, INestedWordAutomaton<LETTER,STATE> newAutomata){
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		s_Logger.info(exitMessage());
	}
	public NwaList(IUltimateServiceProvider services,INestedWordAutomaton<LETTER,STATE> newAutomata,ArrayList<INestedWordAutomaton<LETTER,STATE>> orginalAutomataCollection){
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		s_Logger.info(exitMessage());
	}
	
	/**
	 * Constructs a list that consists of a single automaton.
	 */
	public NwaList(IUltimateServiceProvider services,INestedWordAutomaton<LETTER,STATE> newAutomata){
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		automataCollection = new ArrayList<INestedWordAutomaton<LETTER,STATE>>();
		automataCollection.add(newAutomata);
		s_Logger.info(exitMessage());
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
	public ArrayList<INestedWordAutomaton<LETTER,STATE>> getResult() throws OperationCanceledException {
		return automataCollection;
	}
	/*public String getResult() throws OperationCanceledException {
		return "NwaList_result:"+automataCollection.size();
	}*/
	
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}
	
}
