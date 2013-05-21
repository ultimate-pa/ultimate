package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class DeterminizeDD<LETTER,STATE> extends DoubleDeckerBuilder<LETTER,STATE> 
							  implements IOperation<LETTER,STATE>  {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	protected INestedWordAutomatonOldApi<LETTER,STATE> m_Operand;
	protected IStateDeterminizer<LETTER,STATE> stateDeterminizer;
	protected StateFactory<STATE> contentFactory;
	
	
	/**
	 * Maps a DeterminizedState to its representative in the resulting automaton.
	 */
	protected Map<DeterminizedState<LETTER,STATE>,STATE> det2res =
		new HashMap<DeterminizedState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the DeterminizedState for which it
	 * was created.
	 */
	protected final Map<STATE,DeterminizedState<LETTER,STATE>> res2det =
		new HashMap<STATE, DeterminizedState<LETTER,STATE>>();

	
	@Override
	public String operationName() {
		return "determinizeDD";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
			m_TraversedNwa.sizeInformation();
	}
	
	
	
	
	public DeterminizeDD(INestedWordAutomatonOldApi<LETTER,STATE> input, 
			IStateDeterminizer<LETTER,STATE> stateDeterminizer) 
											throws OperationCanceledException {
		this.contentFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.debug(startMessage());
		this.stateDeterminizer = stateDeterminizer;
		super.m_TraversedNwa = new NestedWordAutomaton<LETTER,STATE>(
				input.getInternalAlphabet(),
				input.getCallAlphabet(),
				input.getReturnAlphabet(),
				input.getStateFactory());
		m_RemoveDeadEnds = false;
		traverseDoubleDeckerGraph();
		assert (m_TraversedNwa.isDeterministic());
		s_Logger.debug(exitMessage());
	}
	
	public DeterminizeDD(INestedWordAutomatonOldApi<LETTER,STATE> input) 
											throws OperationCanceledException {
		this.contentFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.debug(startMessage());
		this.stateDeterminizer = new PowersetDeterminizer<LETTER, STATE>(input);
		super.m_TraversedNwa = new NestedWordAutomaton<LETTER,STATE>(
				input.getInternalAlphabet(),
				input.getCallAlphabet(),
				input.getReturnAlphabet(),
				input.getStateFactory());
		m_RemoveDeadEnds = false;
		traverseDoubleDeckerGraph();
		assert (m_TraversedNwa.isDeterministic());
		s_Logger.debug(exitMessage());
	}

	
	
	
	@Override
	protected Collection<STATE> getInitialStates() {
		ArrayList<STATE> resInitials = 
			new ArrayList<STATE>(m_Operand.getInitialStates().size());
		DeterminizedState<LETTER,STATE> detState = stateDeterminizer.initialState();
		STATE resState = detState.getContent(contentFactory);
		((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(true, detState.containsFinal(), resState);
		det2res.put(detState,resState);
		res2det.put(resState, detState);
		resInitials.add(resState);

		return resInitials;
	}





	@Override
	protected Collection<STATE> buildInternalSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		List<STATE> resInternalSuccessors = new LinkedList<STATE>();
		STATE resState = doubleDecker.getUp();
		
		DeterminizedState<LETTER,STATE> detState = res2det.get(resState);
		
		for (LETTER symbol : m_Operand.getInternalAlphabet()) {
			DeterminizedState<LETTER,STATE> detSucc = 
				stateDeterminizer.internalSuccessor(detState, symbol);
			STATE resSucc = getResState(detSucc);
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(resState, symbol, resSucc);
			resInternalSuccessors.add(resSucc);
		}
		return resInternalSuccessors;
	}
	
	
	@Override
	protected Collection<STATE> buildCallSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		List<STATE> resCallSuccessors = new LinkedList<STATE>();
		STATE resState = doubleDecker.getUp();
		
		DeterminizedState<LETTER,STATE> detState = res2det.get(resState);
		
		for (LETTER symbol : m_Operand.getCallAlphabet()) {
			DeterminizedState<LETTER,STATE> detSucc = 
				stateDeterminizer.callSuccessor(detState, symbol);
			STATE resSucc = getResState(detSucc);
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addCallTransition(resState, symbol, resSucc);
			resCallSuccessors.add(resSucc);
		}
		return resCallSuccessors;
	}


	@Override
	protected Collection<STATE> buildReturnSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		List<STATE> resReturnSuccessors = new LinkedList<STATE>();
		STATE resState = doubleDecker.getUp();
		STATE resLinPred = doubleDecker.getDown();
		DeterminizedState<LETTER,STATE> detState = res2det.get(resState);
		DeterminizedState<LETTER,STATE> detLinPred = res2det.get(resLinPred);
		if (resLinPred == m_TraversedNwa.getEmptyStackState()) {
			return resReturnSuccessors;
		}
		
		for (LETTER symbol : m_Operand.getReturnAlphabet()) {
			DeterminizedState<LETTER,STATE> detSucc = 
				stateDeterminizer.returnSuccessor(detState, detLinPred, symbol);
			STATE resSucc = getResState(detSucc);
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addReturnTransition(resState, resLinPred, symbol, resSucc);
			resReturnSuccessors.add(resSucc);
		}
		return resReturnSuccessors;
	}

	
	
	/**
	 * Get the state in the resulting automaton that represents a
	 * DeterminizedState. If this state in the resulting automaton does not exist
	 * yet, construct it.
	 */
	protected STATE getResState(DeterminizedState<LETTER,STATE> detState) {
		if (det2res.containsKey(detState)) {
			return det2res.get(detState);
		}
		else {
			STATE resState = detState.getContent(contentFactory);
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(false, detState.containsFinal(), resState);
			det2res.put(detState,resState);
			res2det.put(resState,detState);
			return resState;
		}
	}


	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		return super.getResult();
	}


	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		boolean correct = true;
		if (stateDeterminizer instanceof PowersetDeterminizer) {
			s_Logger.info("Testing correctness of determinization");
			INestedWordAutomatonOldApi<LETTER,STATE> resultSadd = (new DeterminizeSadd<LETTER,STATE>(m_Operand)).getResult();
			correct &= (ResultChecker.nwaLanguageInclusion(resultSadd,m_TraversedNwa, stateFactory) == null);
			correct &= (ResultChecker.nwaLanguageInclusion(m_TraversedNwa,resultSadd, stateFactory) == null);
			s_Logger.info("Finished testing correctness of determinization");
		
		}
		return correct;
	}


	
	
	
	
}

