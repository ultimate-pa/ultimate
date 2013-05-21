package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class ComplementDD<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	protected INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	protected INestedWordAutomatonOldApi<LETTER, STATE> m_DeterminizedOperand;
	protected INestedWordAutomatonOldApi<LETTER, STATE> m_Result;

	@Override
	public String operationName() {
		return "complementDD";
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

	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		return m_Result;
	}

	public ComplementDD(INestedWordAutomatonOldApi<LETTER, STATE> operand)
			throws OperationCanceledException {
		m_Operand = operand;

		s_Logger.info(startMessage());
		if (!m_Operand.isDeterministic()) {
			m_DeterminizedOperand = 
				   (new DeterminizeDD<LETTER, STATE>(m_Operand)).getResult();
		} else {
			m_DeterminizedOperand = m_Operand;
			s_Logger.debug("Operand is already deterministic");
		}
		m_Result = new ReachableStatesCopy<LETTER, STATE>(
				m_DeterminizedOperand, true, true, false, false).getResult();
		s_Logger.info(exitMessage());
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		s_Logger.debug("Testing correctness of complement");
		boolean correct = true;
		INestedWordAutomatonOldApi intersectionOperandResult = (new IntersectDD(false, m_Operand, m_Result)).getResult();
		correct &=  ((new IsEmpty(intersectionOperandResult)).getResult() == true);
		s_Logger.debug("Finished testing correctness of complement");
		return correct;
	}

}
