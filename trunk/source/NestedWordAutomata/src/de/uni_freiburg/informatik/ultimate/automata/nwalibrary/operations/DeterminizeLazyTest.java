package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ReachableStatesAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class DeterminizeLazyTest<LETTER,STATE> implements IOperation {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	protected INestedWordAutomaton<LETTER,STATE> m_Operand;
	protected INestedWordAutomaton<LETTER,STATE> m_Result;
	protected IStateDeterminizer<LETTER,STATE> stateDeterminizer;
	protected StateFactory<STATE> contentFactory;
	
	
	@Override
	public String operationName() {
		return "determinizeLazy";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
				m_Result.sizeInformation();
	}
	
	
	
	
	
	public DeterminizeLazyTest(
			INestedWordAutomaton<LETTER,STATE> input) throws OperationCanceledException {
		this.stateDeterminizer = new PowersetDeterminizer<LETTER, STATE>(input);
		this.contentFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.debug(startMessage());
		Det<LETTER, STATE> det = new Det<LETTER, STATE>(input, stateDeterminizer, input.getStateFactory());
		m_Result = new ReachableStatesAutomaton<LETTER, STATE>(det);
		s_Logger.debug(exitMessage());
	}
	






	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult()
			throws OperationCanceledException {
		if (stateDeterminizer instanceof PowersetDeterminizer) {
			assert (ResultChecker.determinize(m_Operand, m_Result));
		}
		return m_Result;
	}


	
	
	
	
}

