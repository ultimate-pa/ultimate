package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class GetAcceptedLassoWord<LETTER, STATE> implements IOperation<LETTER,STATE> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	NestedLassoWord<LETTER> m_AcceptedWord;

	public GetAcceptedLassoWord(INestedWordAutomatonOldApi<LETTER, STATE> operand) throws OperationCanceledException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		BuchiIsEmpty<LETTER, STATE> isEmpty = new BuchiIsEmpty<LETTER, STATE>(operand);
		if (isEmpty.getResult()) {
			throw new IllegalArgumentException(
					"unable to get word from emtpy language");
		} else {
			m_AcceptedWord = isEmpty.getAcceptingNestedLassoRun().getNestedLassoWord();
		}
		s_Logger.info(exitMessage());
	}

	@Override
	public NestedLassoWord<LETTER> getResult() throws OperationCanceledException {
		return m_AcceptedWord;
	}

	@Override
	public String operationName() {
		return "getAcceptedLassoWord";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand "
				+ m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Length of stem: "
				+ m_AcceptedWord.getStem().length() + " Length of loop:" 
				+ m_AcceptedWord.getLoop().length();
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
