package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Determinize;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DeterminizeUnderappox;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.AbstractIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class BuchiComplementRE<LETTER,STATE> implements IOperation {

	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	private INestedWordAutomaton<LETTER,STATE> m_Operand;
	private INestedWordAutomaton<LETTER,STATE> m_Result;
	
	private boolean m_buchiComplementREApplicable;
	
	@Override
	public String operationName() {
		return "buchiComplementRE";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		if (m_buchiComplementREApplicable) {
			return "Finished " + operationName() + " Result " + 
				m_Result.sizeInformation();
		} else {
			return "Unable to perform " + operationName() + "on this input";
		}
	}

	@Override
	public INestedWordAutomaton<LETTER,STATE> getResult() throws OperationCanceledException {
		if (m_buchiComplementREApplicable) {
			return m_Result;
		} else {
			assert m_Result == null;
			throw new UnsupportedOperationException("Operation was not applicable");
		}
	}
	
	
	public BuchiComplementRE(INestedWordAutomaton<LETTER,STATE> operand) throws OperationCanceledException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		INestedWordAutomaton<LETTER,STATE> operandWithoutNonLiveStates = 
				(new ReachableStatesCopy<LETTER,STATE>(operand, false, false, false, true)).getResult();
		if (operandWithoutNonLiveStates.isDeterministic()) {
			s_Logger.info("Rüdigers determinization knack not necessary, already deterministic");
			m_Result = (new BuchiComplementDeterministic<LETTER,STATE>(operandWithoutNonLiveStates)).getResult();
		}
		else {
			PowersetDeterminizer<LETTER,STATE> pd = 
					new PowersetDeterminizer<LETTER,STATE>(operandWithoutNonLiveStates);
			INestedWordAutomaton<LETTER,STATE> determinized = 
					(new DeterminizeUnderappox<LETTER,STATE>(operandWithoutNonLiveStates,pd)).getResult();
			INestedWordAutomaton<LETTER,STATE> determinizedComplement =
					(new BuchiComplementDeterministic<LETTER,STATE>(determinized)).getResult();
			INestedWordAutomaton<LETTER,STATE> intersectionWithOperand =
					(new BuchiIntersect<LETTER,STATE>(true, operandWithoutNonLiveStates, determinizedComplement)).getResult();
			NestedLassoRun<LETTER,STATE> run = (new EmptinessCheck<LETTER,STATE>()).getAcceptingNestedLassoRun(intersectionWithOperand);
			if (run == null) {
				s_Logger.info("Rüdigers determinization knack applicable");
				m_buchiComplementREApplicable = true;
				m_Result = determinizedComplement;
			}
			else {
				s_Logger.info("Rüdigers determinization knack not applicable");
				m_buchiComplementREApplicable = false;
				m_Result = null;
			}
		}


		
		s_Logger.info(exitMessage());
		//assert (ResultChecker.buchiComplement(m_Operand, m_TraversedNwa));
	}
	
	
	/**
	 * Return true if buchiComplementRE was applicable on the input.
	 */
	public boolean applicable() {
		return m_buchiComplementREApplicable;
	}

}
