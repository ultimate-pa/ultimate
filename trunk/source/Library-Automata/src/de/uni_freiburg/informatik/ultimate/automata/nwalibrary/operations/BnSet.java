package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class BnSet<LETTER,STATE> implements IOperation<LETTER,STATE>{

	ArrayList<INestedWordAutomaton<LETTER,STATE>> automataCollection;
	private static Logger s_Logger;
	
	public BnSet(IUltimateServiceProvider services,INestedWordAutomaton<LETTER,STATE> orginalAutomata, INestedWordAutomaton<LETTER,STATE> newAutomata){
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		automataCollection = new ArrayList<INestedWordAutomaton<LETTER,STATE>>();
		automataCollection.add(orginalAutomata);
		automataCollection.add(newAutomata);
		s_Logger.info(exitMessage());
	}
	
	public BnSet(IUltimateServiceProvider services,ArrayList<INestedWordAutomaton<LETTER,STATE>> orginalAutomataCollection, INestedWordAutomaton<LETTER,STATE> newAutomata){
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		s_Logger.info(exitMessage());
	}
	public BnSet(IUltimateServiceProvider services,INestedWordAutomaton<LETTER,STATE> newAutomata,ArrayList<INestedWordAutomaton<LETTER,STATE>> orginalAutomataCollection){
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		s_Logger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "BnSet";
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
		return "BnSet_result:"+automataCollection.size();
	}*/
	
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}
	
}
