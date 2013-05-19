package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Senwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.SenwaWalker.ISuccessorVisitor;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class SenwaBuilder<LETTER, STATE> implements ISuccessorVisitor<LETTER, STATE>, IOperation {
	
	Senwa<LETTER, STATE> m_Senwa;
	INestedWordAutomatonOldApi<LETTER, STATE> m_Nwa;
	Set<STATE> m_Added = new HashSet<STATE>();
	
	Map<STATE,STATE> m_Result2Operand = new HashMap<STATE,STATE>();
	Map<STATE,Map<STATE,STATE>> m_Entry2Operand2Result = new HashMap<STATE,Map<STATE,STATE>>();
	
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	
	@Override
	public String operationName() {
		return "senwa";
	}
	
	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Input has " + 
					m_Nwa.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result has " + 
				m_Senwa.sizeInformation();
	}
	
	
	
	
	
	public SenwaBuilder(INestedWordAutomatonOldApi<LETTER, STATE> nwa) throws OperationCanceledException {
		m_Nwa = nwa;
		s_Logger.info(startMessage());
		m_Senwa = new Senwa<LETTER, STATE>(m_Nwa.getInternalAlphabet(), m_Nwa.getCallAlphabet(), 
				m_Nwa.getReturnAlphabet(), m_Nwa.getStateFactory());
		new SenwaWalker<LETTER, STATE>(m_Senwa, this, true);
		s_Logger.info(exitMessage());
	}
	
	
	
	private STATE getOrConstructResultState(STATE opEntry, STATE opState, boolean isInitial) {
		assert m_Nwa.getStates().contains(opState);
		assert m_Nwa.getStates().contains(opEntry);
		Map<STATE, STATE> op2res = m_Entry2Operand2Result.get(opEntry);
		if (op2res == null) {
			op2res = new HashMap<STATE, STATE>();
			m_Entry2Operand2Result.put(opEntry, op2res);
		}
		STATE resState = op2res.get(opState);
		if (resState == null) {
			resState = m_Nwa.getStateFactory().senwa(opEntry, opState);
			op2res.put(opState, resState);
			m_Result2Operand.put(resState, opState);
			STATE resEntry = op2res.get(opEntry);
			assert resEntry != null;
			m_Senwa.addState(resState, isInitial, m_Nwa.isFinal(opState), resEntry);
		}
		return resState;
	}
	
	private STATE getOperandState(STATE resState) {
		assert m_Senwa.getStates().contains(resState);
		STATE opState = m_Result2Operand.get(resState);
		assert opState != null;
		return opState;
	}
	

	@Override
	public Iterable<STATE> getInitialStates() {
		Set<STATE> resInits = new HashSet<STATE>();
		for (STATE opState : m_Nwa.getInitialStates()) {
			STATE resSTATE = getOrConstructResultState(opState, opState, true);
			resInits.add(resSTATE);
		}
		return resInits;
	}

	@Override
	public Iterable<STATE> visitAndGetInternalSuccessors(STATE resState) {
		STATE resEntry = m_Senwa.getEntry(resState);
		STATE opEntry = getOperandState(resEntry);
		Set<STATE> resSuccs = new HashSet<STATE>();
		STATE opState = getOperandState(resState);
		for (LETTER letter : m_Nwa.lettersInternal(opState)) {
			for (STATE opSucc : m_Nwa.succInternal(opState, letter)) {
				STATE resSucc = getOrConstructResultState(opEntry, opSucc, false);
				resSuccs.add(resSucc);
				m_Senwa.addInternalTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetCallSuccessors(STATE resState) {
		Set<STATE> resSuccs = new HashSet<STATE>();
		STATE opState = getOperandState(resState);
		for (LETTER letter : m_Nwa.lettersCall(opState)) {
			for (STATE opSucc : m_Nwa.succCall(opState, letter)) {
				STATE resSucc = getOrConstructResultState(opSucc, opSucc, false);
				resSuccs.add(resSucc);
				m_Senwa.addCallTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetReturnSuccessors(STATE resState,
			STATE resHier) {
		STATE opState = getOperandState(resState);
		STATE opHier = getOperandState(resHier);
		STATE resHierEntry = m_Senwa.getEntry(resHier);
		STATE opHierEntry = getOperandState(resHierEntry);
		Set<STATE> resSuccs = new HashSet<STATE>();
		for (LETTER letter : m_Nwa.lettersReturn(opState)) {
			for (STATE opSucc : m_Nwa.succReturn(opState, opHier, letter)) {
				STATE resSucc = getOrConstructResultState(opHierEntry, opSucc, false);
				resSuccs.add(resSucc);
				m_Senwa.addReturnTransition(resState, resHier, letter, resSucc);
			}
		}
		return resSuccs;
	}
	
	public Senwa<LETTER,STATE> getResult() throws OperationCanceledException {
		assert ResultChecker.minimize(m_Nwa, m_Senwa) : 
			"Result recognizes differnt language";
		return m_Senwa;
	}

}
