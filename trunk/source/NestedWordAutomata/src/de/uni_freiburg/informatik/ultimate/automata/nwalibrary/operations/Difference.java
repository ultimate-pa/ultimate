package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class Difference<LETTER,STATE> implements IOperation<LETTER,STATE>, IOpWithDelayedDeadEndRemoval<LETTER, STATE> {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_FstOperand;
	private final INestedWordAutomatonSimple<LETTER,STATE> m_SndOperand;
	private DeterminizeNwa<LETTER,STATE> m_SndDeterminized;
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	private ComplementDeterministicNwa<LETTER,STATE> m_SndComplemented;
	private IntersectNwa<LETTER, STATE> m_Intersect;
	private NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;
	private NestedWordAutomatonFilteredStates<LETTER, STATE> m_ResultWOdeadEnds;
	private final StateFactory<STATE> m_StateFactory;
	
	
	@Override
	public String operationName() {
		return "difference";
	}
	
	
	@Override
	public String startMessage() {
		return "Start intersect. First operand " + 
				m_FstOperand.sizeInformation() + ". Second operand " + 
				m_SndOperand.sizeInformation();	
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
				m_Result.sizeInformation();
	}
	
	
	
	
	public Difference(INestedWordAutomatonOldApi<LETTER,STATE> fstOperand,
			INestedWordAutomatonOldApi<LETTER,STATE> sndOperand
			) throws AutomataLibraryException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = m_FstOperand.getStateFactory();
		m_StateDeterminizer = new PowersetDeterminizer<LETTER,STATE>(sndOperand);
		s_Logger.info(startMessage());
		computateDifference(false);
		s_Logger.info(exitMessage());
	}
	
	
	public Difference(INestedWordAutomatonOldApi<LETTER,STATE> fstOperand,
			INestedWordAutomatonOldApi<LETTER,STATE> sndOperand,
			IStateDeterminizer<LETTER, STATE> stateDeterminizer,
			StateFactory<STATE> sf,
			boolean finalIsTrap) throws AutomataLibraryException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = sf;
		m_StateDeterminizer = stateDeterminizer;
		s_Logger.info(startMessage());
		computateDifference(finalIsTrap);
		s_Logger.info(exitMessage());
	}
	
	private void computateDifference(boolean finalIsTrap) throws AutomataLibraryException {
		if (m_StateDeterminizer instanceof PowersetDeterminizer) {
			TotalizeNwa<LETTER, STATE> sndTotalized = new TotalizeNwa<LETTER, STATE>(m_SndOperand, m_StateFactory);
			ComplementDeterministicNwa<LETTER,STATE> sndComplemented = new ComplementDeterministicNwa<LETTER, STATE>(sndTotalized);
			IntersectNwa<LETTER, STATE> intersect = new IntersectNwa<LETTER, STATE>(m_FstOperand, sndComplemented, m_StateFactory, finalIsTrap);
			NestedWordAutomatonReachableStates<LETTER, STATE> result = new NestedWordAutomatonReachableStates<LETTER, STATE>(intersect);
			if (!sndTotalized.nonDeterminismInInputDetected()) {
				m_SndComplemented = sndComplemented;
				m_Intersect = intersect;
				m_Result = result;
				s_Logger.warn("Subtrahend was deterministic. Have not used determinization.");
				return;
			} else {
			s_Logger.warn("Subtrahend was not deterministic. Recomputing result with determinization.");
			}
		}
		m_SndDeterminized = new DeterminizeNwa<LETTER,STATE>(m_SndOperand,m_StateDeterminizer,m_StateFactory);
		m_SndComplemented = new ComplementDeterministicNwa<LETTER, STATE>(m_SndDeterminized);
		m_Intersect = new IntersectNwa<LETTER, STATE>(m_FstOperand, m_SndComplemented, m_StateFactory, finalIsTrap);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Intersect);
	}
	






	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		if (m_ResultWOdeadEnds == null) {
			return m_Result;
		} else {
			return m_ResultWOdeadEnds;
		}
	}


	
	public boolean checkResult(StateFactory<STATE> sf) throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		INestedWordAutomatonOldApi<LETTER, STATE> fstOperandOldApi = ResultChecker.getOldApiNwa(m_FstOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> sndOperandOldApi = ResultChecker.getOldApiNwa(m_SndOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> resultDD = 
				(new DifferenceDD<LETTER, STATE>(fstOperandOldApi,sndOperandOldApi, 
						new PowersetDeterminizer<LETTER, STATE>(sndOperandOldApi),sf,false,false)).getResult();
		boolean correct = true;
//		correct &= (resultDD.size() == m_Result.size());
//		assert correct;
		correct &= (ResultChecker.nwaLanguageInclusion(resultDD, m_Result, sf) == null);
		assert correct;
		correct &= (ResultChecker.nwaLanguageInclusion(m_Result, resultDD, sf) == null);
		assert correct;
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_FstOperand,m_SndOperand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}





	@Override
	public boolean removeDeadEnds() {
		m_ResultWOdeadEnds = new NestedWordAutomatonFilteredStates<LETTER, STATE>(m_Result);
		s_Logger.info("With dead ends: " + m_Result.getStates().size());
		s_Logger.info("Without dead ends: " + m_ResultWOdeadEnds.getStates().size());
		return m_Result.getStates().size() != m_ResultWOdeadEnds.getStates().size();
	}


	@Override
	public long getDeadEndRemovalTime() {
		// TODO Auto-generated method stub
		return 0;
	}


	@Override
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
		return m_Result.getRemovedUpDownEntry();
	}
	
	
	
}

