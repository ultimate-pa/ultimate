package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Class that provides the Buchi emptiness check for nested word automata. 
 * 
 * @param <LETTER> Symbol. Type of the symbols used as alphabet.
 * @param <STATE> Content. Type of the labels (the content) of the automata states. 
 * @version 2010-12-18
 */
public class BuchiIsEmpty<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	
	INestedWordAutomatonSimple<LETTER, STATE> m_Nwa;
	NestedWordAutomatonReachableStates<LETTER, STATE> m_Reach;
	NestedWordAutomatonReachableStates<LETTER, STATE>.StronglyConnectedComponents m_Sccs;
	final Boolean m_Result;
	
	public BuchiIsEmpty(INestedWordAutomatonSimple<LETTER, STATE> nwa) throws OperationCanceledException {
		m_Nwa = nwa;
		s_Logger.info(startMessage());
		if (m_Nwa instanceof NestedWordAutomatonReachableStates) {
			m_Reach = (NestedWordAutomatonReachableStates<LETTER, STATE>) m_Nwa;
		} else {
			m_Reach = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Nwa);
		}
		m_Sccs = m_Reach.getOrComputeStronglyConnectedComponents();
		m_Result = m_Sccs.buchiIsEmpty();
		s_Logger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "buchiIsEmpty";
	}

	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Operand " + 
			m_Nwa.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result is " + m_Result; 
	}

	@Override
	public Boolean getResult() throws OperationCanceledException {
		return m_Result;
	}
	

	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);	
	
	
	public NestedLassoRun<LETTER,STATE> getAcceptingNestedLassoRun() throws OperationCanceledException {
		if (m_Result) {
			s_Logger.info("There is no accepting nested lasso run");
			return null;
		} else {
			s_Logger.info("Starting construction of run");
			return m_Sccs.getNestedLassoRun();
		}
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}



}
