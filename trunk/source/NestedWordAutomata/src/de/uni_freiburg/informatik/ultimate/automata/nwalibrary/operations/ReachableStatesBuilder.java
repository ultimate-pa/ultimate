package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INWA;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class ReachableStatesBuilder<LETTER, STATE> extends DoubleDeckerVisitor<LETTER, STATE> implements IOperation {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	public ReachableStatesBuilder(
			INestedWordAutomaton<LETTER,STATE> automaton,
			boolean removeDeadEnds,
			boolean removeNonLiveStates) throws OperationCanceledException {
		s_Logger.info(startMessage());

		super.m_TraversedNwa = (NestedWordAutomaton<LETTER, STATE>) automaton;
//		super.m_RemoveDeadEnds = removeDeadEnds;
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER,STATE>) super.m_TraversedNwa).setUp2Down(getUp2DownMapping());
		s_Logger.info(exitMessage());
	}
	
	
	@Override
	public String operationName() {
		return "reachable states";
	}
	
	@Override
	public String startMessage() {
			return "Start " + operationName() + ". ";
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
		m_TraversedNwa.sizeInformation();
	}
	
	
	@Override
	protected Collection<STATE> getInitialStates() {
		return m_TraversedNwa.getInitialStates();
	}

	@Override
	protected Collection<STATE> visitAndGetInternalSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Set<STATE> succs = new HashSet<STATE>();
		for (OutgoingInternalTransition<LETTER, STATE> out : ((INWA<LETTER, STATE>) m_TraversedNwa).internalSuccessors(doubleDecker.getUp())) {
			succs.add(out.getSucc());
		}
		return succs;
	}

	@Override
	protected Collection<STATE> visitAndGetCallSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Set<STATE> succs = new HashSet<STATE>();
		for (OutgoingCallTransition<LETTER, STATE> out : ((INWA<LETTER, STATE>) m_TraversedNwa).callSuccessors(doubleDecker.getUp())) {
			succs.add(out.getSucc());
		}
		return succs;
	}

	@Override
	protected Collection<STATE> visitAndGetReturnSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Set<STATE> succs = new HashSet<STATE>();
		for (OutgoingReturnTransition<LETTER, STATE> out : ((INWA<LETTER, STATE>) m_TraversedNwa).returnSuccessors(doubleDecker.getUp())) {
			succs.add(out.getSucc());
		}
		return succs;
	}



}
