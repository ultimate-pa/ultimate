package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class Automaton2Net<LETTER, STATE> implements IOperation {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	INestedWordAutomaton<LETTER, STATE> m_Operand;
	IPetriNet<LETTER, STATE> m_Net;

	public Automaton2Net(INestedWordAutomaton<LETTER, STATE> operand) throws OperationCanceledException {
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
		return "bfsEmptiness";
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

}
