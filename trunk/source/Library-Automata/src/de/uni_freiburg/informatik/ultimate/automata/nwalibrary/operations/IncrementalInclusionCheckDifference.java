package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.InclusionViaDifference;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class IncrementalInclusionCheckDifference<LETTER, STATE> extends InclusionViaDifference<LETTER, STATE> implements IOperation<LETTER, STATE> {
	private static Logger s_Logger;
	public  IncrementalInclusionCheckDifference(
			IUltimateServiceProvider services, 
			StateFactory<STATE> stateFactory, 
			INestedWordAutomatonSimple<LETTER, STATE> a, 
			List<INestedWordAutomatonSimple<LETTER, STATE>> b) throws AutomataLibraryException {
		super(services,stateFactory,a);
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		for (INestedWordAutomatonSimple<LETTER, STATE> bi : b) {
			addSubtrahend(bi);
		}
		// obtain counterexample, counterexample is null if inclusion holds
		s_Logger.info(exitMessage());
	}
	public String operationName() {
		return "IncrementalInclusionCheckDifference";
	}
	@Override
	public String startMessage() {
		return "Start " + operationName();
	}
	
	@Override
	public String exitMessage() {
		return "Exit " + operationName();
	}
	public Boolean getResult() throws OperationCanceledException{
		return getCounterexample() == null;
	}
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return true;
	}
}
