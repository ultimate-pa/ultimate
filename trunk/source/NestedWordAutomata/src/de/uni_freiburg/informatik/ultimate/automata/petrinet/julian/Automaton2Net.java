package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class Automaton2Net<LETTER, STATE> implements IOperation<LETTER,STATE> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	IPetriNet<LETTER, STATE> m_Net;

	public Automaton2Net(INestedWordAutomatonOldApi<LETTER, STATE> operand) throws AutomataLibraryException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		m_Net = new PetriNetJulian<LETTER, STATE>(m_Operand);
		s_Logger.info(exitMessage());
	}

	@Override
	public IPetriNet<LETTER, STATE> getResult() throws OperationCanceledException {
		return m_Net;
	}

	@Override
	public String operationName() {
		return "automaton2net";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand "
				+ m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". PetriNet "
				+ m_Net.sizeInformation();
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
