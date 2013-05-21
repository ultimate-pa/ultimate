package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder.order;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class IsEmpty<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	private final PetriNetJulian<LETTER,STATE> m_Operand;
	private final Boolean m_Result;
	
	public IsEmpty(PetriNetJulian<LETTER,STATE> operand) throws OperationCanceledException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		PetriNetUnfolder<LETTER,STATE> unf = 
				new PetriNetUnfolder<LETTER,STATE>(operand, order.ERV, false, true);
		PetriNetRun<LETTER,STATE> run = unf.getAcceptingRun();
		m_Result = (run == null);
		s_Logger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "isEmpty";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() +
			"Operand " + m_Operand.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() +
			" language " + (m_Result ? "is empty" : "is not emtpy");
	}

	@Override
	public Boolean getResult() throws OperationCanceledException {
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		// TODO Auto-generated method stub
		return false;
	}

}
