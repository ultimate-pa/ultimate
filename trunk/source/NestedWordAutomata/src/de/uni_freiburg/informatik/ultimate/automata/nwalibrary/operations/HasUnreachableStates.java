package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DoubleDeckerVisitor;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Check if an NWA contains states which are not reachable in any run.
 * Does not change the input automaton.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class HasUnreachableStates<LETTER,STATE> extends DoubleDeckerVisitor<LETTER,STATE>
										   implements IOperation<LETTER,STATE> {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	
	private final Set<STATE> m_VisitedStates = new HashSet<STATE>();
	private int m_UnreachalbeStates = 0;

	
	public HasUnreachableStates(INestedWordAutomatonOldApi<LETTER,STATE> operand) throws OperationCanceledException {
		m_TraversedNwa = operand;
		s_Logger.info(startMessage());
		traverseDoubleDeckerGraph();
		for (STATE state : m_TraversedNwa.getStates()) {
			if (!m_VisitedStates.contains(state)) {
				m_UnreachalbeStates++;
				s_Logger.warn("Unreachalbe state: " + state);
			}
		}
		s_Logger.info(exitMessage());
	}

	@Override
	protected Collection<STATE> getInitialStates() {
		m_VisitedStates.addAll(m_TraversedNwa.getInitialStates());
		return m_TraversedNwa.getInitialStates();
	}

	@Override
	protected Collection<STATE> visitAndGetInternalSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		STATE state = doubleDecker.getUp();
		Set<STATE> succs = new HashSet<STATE>();
		for (LETTER letter : m_TraversedNwa.lettersInternal(state)) {
			for (STATE succ : m_TraversedNwa.succInternal(state, letter)) {
				succs.add(succ);
			}
		}
		m_VisitedStates.addAll(succs);
		return succs;
	}
	
	

	@Override
	protected Collection<STATE> visitAndGetCallSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		STATE state = doubleDecker.getUp();
		Set<STATE> succs = new HashSet<STATE>();
		for (LETTER letter : m_TraversedNwa.lettersCall(state)) {
			for (STATE succ : m_TraversedNwa.succCall(state, letter)) {
				succs.add(succ);
			}
		}
		m_VisitedStates.addAll(succs);
		return succs;
	}
	
	

	@Override
	protected Collection<STATE> visitAndGetReturnSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		STATE state = doubleDecker.getUp();
		STATE hier = doubleDecker.getDown();
		Set<STATE> succs = new HashSet<STATE>();
		for (LETTER letter : m_TraversedNwa.lettersReturn(state)) {
			for (STATE succ : m_TraversedNwa.succReturn(state, hier, letter)) {
				succs.add(succ);
			}
		}
		m_VisitedStates.addAll(succs);
		return succs;
	}

	@Override
	public String operationName() {
		return "detectUnreachableStates";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_TraversedNwa.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand has " + 
			m_UnreachalbeStates + " unreachalbe states";
	}
	
	public boolean result() {
		return m_UnreachalbeStates != 0;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}
	

}
