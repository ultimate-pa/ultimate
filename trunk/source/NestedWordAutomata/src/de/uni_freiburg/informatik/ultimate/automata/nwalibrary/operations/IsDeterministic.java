package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class IsDeterministic<LETTER,STATE> implements IOperation<LETTER,STATE> {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	private final TotalizeNwa<LETTER, STATE> m_Totalized;
	private NestedWordAutomatonReachableStates<LETTER, STATE> m_Reach;
	private boolean m_Result;
	private final StateFactory<STATE> m_StateFactory;
	
	
	@Override
	public String operationName() {
		return "isDeterministic";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand is " 
					+ (m_Result ? "" : "not") + "deterministic."; 
	}
	
	
	public IsDeterministic(INestedWordAutomatonSimple<LETTER,STATE> input) throws OperationCanceledException {
		this.m_StateFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.info(startMessage());
		m_Totalized = new TotalizeNwa<LETTER, STATE>(input, m_StateFactory);
		boolean inputIsDeterministic = false;
		try {
			m_Reach = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Totalized);
			inputIsDeterministic = true;
		} catch (IllegalArgumentException e) {
			if (e.getMessage().equals(TotalizeNwa.OPERAND_NOT_DETERMINISTIC)) {
				inputIsDeterministic = false;
			}
		}
		m_Result = inputIsDeterministic;
		s_Logger.info(exitMessage());
	}
	


	@Override
	public Boolean getResult() {
		return m_Result;
	}


	@Override
	public boolean checkResult(StateFactory<STATE> sf) throws AutomataLibraryException {
		boolean correct = true;
		if (m_Result) {
			s_Logger.info("Start testing correctness of " + operationName());
			INestedWordAutomatonOldApi<LETTER, STATE> operandOldApi = ResultChecker.getOldApiNwa(m_Operand);
			// should recognize same language as old computation
			correct &= (ResultChecker.nwaLanguageInclusion(operandOldApi, m_Reach, sf) == null);
			assert correct;
			correct &= (ResultChecker.nwaLanguageInclusion(m_Reach, operandOldApi, sf) == null);
			assert correct;
			if (!correct) {
				ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_Operand);
			}
		s_Logger.info("Finished testing correctness of " + operationName());
		} else {
			s_Logger.warn("result was not tested");
		}
		return correct;
	}
	
	
}

