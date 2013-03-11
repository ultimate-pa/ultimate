package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class ComplementSadd<LETTER, STATE> implements IOperation {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	protected INestedWordAutomaton<LETTER, STATE> m_Operand;
	protected INestedWordAutomaton<LETTER, STATE> m_DeterminizedOperand;
	protected INestedWordAutomaton<LETTER, STATE> m_Result;

	@Override
	public String operationName() {
		return "complementSadd";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand "
				+ m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_Result.sizeInformation();
	}

	public INestedWordAutomaton<LETTER, STATE> getResult()
											throws OperationCanceledException {
		assert (ResultChecker.complement(m_Operand, m_Result));
		return m_Result;
	}

	public ComplementSadd(INestedWordAutomaton<LETTER, STATE> operand)
											throws OperationCanceledException {
		m_Operand = operand;

		s_Logger.info(startMessage());
		if (!m_Operand.isDeterministic()) {
			m_DeterminizedOperand = 
					(new DeterminizeSadd<LETTER, STATE>(m_Operand)).getResult();
		} else {
			m_DeterminizedOperand = m_Operand;
			s_Logger.debug("Operand is already deterministic");
		}
		m_Result = new ReachableStatesCopy<LETTER, STATE>(
				m_DeterminizedOperand, true, true, false, false).getResult();
		s_Logger.info(exitMessage());
	}

}
