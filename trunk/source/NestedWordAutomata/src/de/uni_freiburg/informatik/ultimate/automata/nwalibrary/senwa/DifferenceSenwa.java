package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Senwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.StateDeterminizerCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceSadd;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.SenwaWalker.ISuccessorVisitor;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class DifferenceSenwa<LETTER, STATE> implements 
								ISuccessorVisitor<LETTER, STATE>,
								IOperation<LETTER, STATE>,
								IOpWithDelayedDeadEndRemoval<LETTER, STATE>{
	
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
		
	private final INestedWordAutomatonOldApi<LETTER,STATE> minuend;
	private final INestedWordAutomatonOldApi<LETTER,STATE> subtrahend;
	
	private final IStateDeterminizer<LETTER,STATE> stateDeterminizer;
	
	private final StateFactory<STATE> contentFactory;

	private final Senwa<LETTER, STATE> m_Senwa;
	
	private final SenwaWalker<LETTER, STATE> m_SenwaWalker;
	
	
	
	
	
	/**
	 * Maps a state in resulting automaton to the DifferenceState for which it
	 * was created.
	 */
	Map<STATE,DifferenceState<LETTER,STATE>> m_Result2Operand = 
			new HashMap<STATE,DifferenceState<LETTER,STATE>>();
	
	/**
	 * Maps a DifferenceState and an entry state to its representative in the
	 * resulting automaton.
	 */
	Map<DifferenceState<LETTER,STATE>,Map<DifferenceState<LETTER,STATE>,STATE>> m_Entry2Operand2Result = 
			new HashMap<DifferenceState<LETTER,STATE>,Map<DifferenceState<LETTER,STATE>,STATE>>();
	
	
	
	
	@Override
	public String operationName() {
		return "differenceSenwa";
	}
	
	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Minuend " + 
			minuend.sizeInformation() + ". Subtrahend " + 
			subtrahend.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
		m_Senwa.sizeInformation() + ". Max degree of Nondeterminism is " + 
		stateDeterminizer.getMaxDegreeOfNondeterminism();
	}
	
	
	
	
	public DifferenceSenwa(
			INestedWordAutomatonOldApi<LETTER,STATE> minuend,
			INestedWordAutomatonOldApi<LETTER,STATE> subtrahend)
					throws OperationCanceledException {
		contentFactory = minuend.getStateFactory();
		this.minuend = minuend;
		this.subtrahend = subtrahend;
		s_Logger.info(startMessage());
		
		
		this.stateDeterminizer = new StateDeterminizerCache<LETTER, STATE>(
							new PowersetDeterminizer<LETTER,STATE>(subtrahend)); 
		
		m_Senwa = new Senwa<LETTER, STATE>(minuend.getInternalAlphabet(), minuend.getCallAlphabet(), 
				minuend.getReturnAlphabet(), minuend.getStateFactory());
		m_SenwaWalker = new SenwaWalker<LETTER, STATE>(m_Senwa, this, true);
		s_Logger.info(exitMessage());
	}
	
	
	public DifferenceSenwa(
			INestedWordAutomatonOldApi<LETTER,STATE> minuend,
			INestedWordAutomatonOldApi<LETTER,STATE> subtrahend,
			IStateDeterminizer<LETTER,STATE> stateDeterminizer,
			boolean removeDeadEndsImmediately)
					throws OperationCanceledException {
		contentFactory = minuend.getStateFactory();
		this.minuend = minuend;
		this.subtrahend = subtrahend;
		s_Logger.info(startMessage());
		
		
		this.stateDeterminizer = new StateDeterminizerCache<LETTER, STATE>(
				stateDeterminizer); 
		
		m_Senwa = new Senwa<LETTER, STATE>(minuend.getInternalAlphabet(), minuend.getCallAlphabet(), 
				minuend.getReturnAlphabet(), minuend.getStateFactory());
		m_SenwaWalker = new SenwaWalker<LETTER, STATE>(m_Senwa, this, removeDeadEndsImmediately);
		s_Logger.info(exitMessage());
	}
	
	
	
	
	
	private STATE getOrConstructResultState(
			DifferenceState<LETTER,STATE> diffEntry, 
			DifferenceState<LETTER,STATE> diffState, boolean isInitial) {
		assert minuend.getStates().contains(diffState.getMinuendState());
		assert minuend.getStates().contains(diffEntry.getMinuendState());
		Map<DifferenceState<LETTER,STATE>, STATE> op2res = m_Entry2Operand2Result.get(diffEntry);
		if (op2res == null) {
			op2res = new HashMap<DifferenceState<LETTER,STATE>, STATE>();
			m_Entry2Operand2Result.put(diffEntry, op2res);
		}
		STATE resState = op2res.get(diffState);
		if (resState == null) {
			
			resState = contentFactory.senwa(
					diffEntry.getState(contentFactory), 
					diffState.getState(contentFactory));
			op2res.put(diffState, resState);
			m_Result2Operand.put(resState, diffState);
			STATE resEntry = op2res.get(diffEntry);
			assert resEntry != null;
			m_Senwa.addState(resState, isInitial, diffState.isFinal(), resEntry);
		}
		return resState;
	}
	
	private DifferenceState<LETTER,STATE> getOperandState(STATE resState) {
		assert m_Senwa.getStates().contains(resState);
		DifferenceState<LETTER,STATE> opState = m_Result2Operand.get(resState);
		assert opState != null;
		return opState;
	}
	

	@Override
	public Iterable<STATE> getInitialStates() {
		
		ArrayList<STATE> resInitials = 
				new ArrayList<STATE>(subtrahend.getInitialStates().size());
		DeterminizedState<LETTER,STATE> detState = stateDeterminizer.initialState();
		for (STATE minuState : minuend.getInitialStates()) {
			boolean isFinal = minuend.isFinal(minuState) &&
											!detState.containsFinal();
			DifferenceState<LETTER,STATE> diffState = 
				new DifferenceState<LETTER,STATE>(minuState, detState, isFinal);
			STATE resState = getOrConstructResultState(diffState, diffState, true); 
			resInitials.add(resState);
		}
		return resInitials;
	}

	@Override
	public Iterable<STATE> visitAndGetInternalSuccessors(STATE resState) {
		STATE resEntry = m_Senwa.getEntry(resState);
		DifferenceState<LETTER,STATE> diffEntry = getOperandState(resEntry);
		Set<STATE> resSuccs = new HashSet<STATE>();
		DifferenceState<LETTER,STATE> diffState = getOperandState(resState);
		STATE minuState = diffState.getMinuendState();
		DeterminizedState<LETTER,STATE> subtrState = diffState.getSubtrahendDeterminizedState();
		for (LETTER letter : minuend.lettersInternal(minuState)) {
			for (STATE minuSucc : minuend.succInternal(minuState, letter)) {
				DeterminizedState<LETTER, STATE> subtrSucc = stateDeterminizer.internalSuccessor(subtrState, letter);
				boolean isFinal = minuend.isFinal(minuSucc) &&
						!subtrSucc.containsFinal();
				DifferenceState<LETTER, STATE> diffSucc = new DifferenceState<LETTER,STATE>(minuSucc, subtrSucc, isFinal);		
				
				STATE resSucc = getOrConstructResultState(diffEntry, diffSucc, false);
				resSuccs.add(resSucc);
				m_Senwa.addInternalTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetCallSuccessors(STATE resState) {
		Set<STATE> resSuccs = new HashSet<STATE>();
		DifferenceState<LETTER,STATE> diffState = getOperandState(resState);
		STATE minuState = diffState.getMinuendState();
		DeterminizedState<LETTER,STATE> subtrState = 
									diffState.getSubtrahendDeterminizedState();
		for (LETTER letter : minuend.lettersCall(minuState)) {
			for (STATE minuSucc : minuend.succCall(minuState, letter)) {
				DeterminizedState<LETTER, STATE> subtrSucc = 
						stateDeterminizer.callSuccessor(subtrState, letter);
				boolean isFinal = minuend.isFinal(minuSucc) &&
						!subtrSucc.containsFinal();
				DifferenceState<LETTER, STATE> diffSucc = new 
						DifferenceState<LETTER,STATE>(minuSucc, subtrSucc, isFinal);		
				STATE resSucc = getOrConstructResultState(diffSucc, diffSucc, false);
				resSuccs.add(resSucc);
				m_Senwa.addCallTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetReturnSuccessors(STATE resState,
			STATE resHier) {
		Set<STATE> resSuccs = new HashSet<STATE>();
		DifferenceState<LETTER,STATE> diffState = getOperandState(resState);
		STATE minuState = diffState.getMinuendState();
		DeterminizedState<LETTER,STATE> subtrState = 
									diffState.getSubtrahendDeterminizedState();
		DifferenceState<LETTER,STATE> diffHier = getOperandState(resHier);
		STATE minuHier = diffHier.getMinuendState();
		DeterminizedState<LETTER,STATE> subtrHier = 
									diffHier.getSubtrahendDeterminizedState();
		STATE resHierEntry = m_Senwa.getEntry(resHier);
		DifferenceState<LETTER,STATE> diffHierEntry = getOperandState(resHierEntry);

		for (LETTER letter : minuend.lettersReturn(minuState)) {
			for (STATE minuSucc : minuend.succReturn(minuState, minuHier, letter)) {
				DeterminizedState<LETTER, STATE> subtrSucc = 
						stateDeterminizer.returnSuccessor(subtrState, subtrHier, letter);
				boolean isFinal = minuend.isFinal(minuSucc) &&
						!subtrSucc.containsFinal();
				DifferenceState<LETTER, STATE> diffSucc = new 
						DifferenceState<LETTER,STATE>(minuSucc, subtrSucc, isFinal);		
				STATE resSucc = getOrConstructResultState(diffHierEntry, diffSucc, false);
				resSuccs.add(resSucc);
				m_Senwa.addReturnTransition(resState, resHier, letter, resSucc);
			}
		}
		return resSuccs;
	}
	
	public Senwa<LETTER,STATE> getResult() throws OperationCanceledException {
		return m_Senwa;
	}
	
	
//FIXME: Remove this
	public boolean removeStatesThatCanNotReachFinal(
			boolean computeRemovedDoubleDeckersAndCallSuccessors) {
		return m_SenwaWalker.removeStatesThatCanNotReachFinal(
								computeRemovedDoubleDeckersAndCallSuccessors);
	}

	
	public long getDeadEndRemovalTime() {
		return m_SenwaWalker.getDeadEndRemovalTime();
	}

	@Override
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean removeDeadEnds() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean correct = true;
		if (stateDeterminizer instanceof PowersetDeterminizer) {
			s_Logger.info("Start testing correctness of " + operationName());

			INestedWordAutomatonOldApi<LETTER,STATE> resultSadd = (new DifferenceSadd<LETTER,STATE>(minuend, subtrahend)).getResult();
			correct &= (ResultChecker.nwaLanguageInclusion(resultSadd, m_Senwa, stateFactory) == null);
			correct &= (ResultChecker.nwaLanguageInclusion(m_Senwa, resultSadd, stateFactory) == null);
			if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", minuend,subtrahend);
			}
			s_Logger.info("Finished testing correctness of " + operationName());
		} else {
			s_Logger.warn("Unable to test correctness if state determinzier is not the PowersetDeterminizer.");
		}
		return correct;
	}

}
