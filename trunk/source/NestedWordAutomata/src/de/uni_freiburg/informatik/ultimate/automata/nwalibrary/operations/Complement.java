package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class Complement<LETTER,STATE> implements IOperation {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	private final DeterminizeNwa<LETTER,STATE> m_Determinized;
	private final ComplementDeterministicNwa<LETTER,STATE> m_Complement;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	private final StateFactory<STATE> m_StateFactory;
	
	
	@Override
	public String operationName() {
		return "complement";
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
	
	
	public Complement(INestedWordAutomatonSimple<LETTER,STATE> operand, 
			IStateDeterminizer<LETTER,STATE> stateDeterminizer, 
			StateFactory<STATE> sf) throws OperationCanceledException {
		m_Operand = operand;
		m_StateDeterminizer = stateDeterminizer;
		m_StateFactory = sf;
		if (operand instanceof DeterminizeNwa) {
			m_Determinized = (DeterminizeNwa<LETTER, STATE>) operand;
		} else {
			m_Determinized = new DeterminizeNwa<LETTER, STATE>(operand, m_StateDeterminizer, m_StateFactory);
		}
		s_Logger.info(startMessage());
		m_Complement = new ComplementDeterministicNwa<LETTER, STATE>(m_Determinized);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Complement);
		s_Logger.info(exitMessage());
	}
	
	public Complement(INestedWordAutomatonSimple<LETTER,STATE> operand) throws OperationCanceledException {
		m_Operand = operand;
		m_StateDeterminizer = new PowersetDeterminizer<LETTER, STATE>(operand);
		m_StateFactory = operand.getStateFactory();
		if (operand instanceof DeterminizeNwa) {
			m_Determinized = (DeterminizeNwa<LETTER, STATE>) operand;
		} else {
			m_Determinized = new DeterminizeNwa<LETTER, STATE>(operand, m_StateDeterminizer, m_StateFactory);
		}
		s_Logger.info(startMessage());
		m_Complement = new ComplementDeterministicNwa<LETTER, STATE>(m_Determinized);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Complement);
		s_Logger.info(exitMessage());
	}
	



	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		if (m_StateDeterminizer instanceof PowersetDeterminizer) {
			assert (checkResult(m_StateFactory));
		}
		return m_Result;
	}
	
	
	
	public boolean checkResult(StateFactory<STATE> sf) throws OperationCanceledException {
		s_Logger.info("Start testing correctness of " + operationName());
		INestedWordAutomatonOldApi<LETTER, STATE> operandOldApi = ResultChecker.getOldApiNwa(m_Operand);
		
		boolean correct = true;
		// intersection of operand and result should be empty
		INestedWordAutomatonOldApi<LETTER, STATE> intersectionOperandResult = 
				(new IntersectDD<LETTER, STATE>(operandOldApi, m_Result)).getResult();
		correct &= (new IsEmpty<LETTER, STATE>(intersectionOperandResult)).getResult();
		INestedWordAutomatonOldApi<LETTER, STATE> resultDD = (new ComplementDD<LETTER, STATE>(operandOldApi)).getResult();
		// should have same number of states as old complementation
		// does not hold, resultDD sometimes has additional sink state
//		correct &= (resultDD.size() == m_Result.size());
		// should recognize same language as old computation
		correct &= (ResultChecker.nwaLanguageInclusion(resultDD, m_Result, sf) == null);
		correct &= (ResultChecker.nwaLanguageInclusion(m_Result, resultDD, sf) == null);
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_Operand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
}