package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class Difference<LETTER,STATE> implements IOperation<LETTER,STATE> {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_FstOperand;
	private final INestedWordAutomatonSimple<LETTER,STATE> m_SndOperand;
	private final DeterminizeNwa<LETTER,STATE> m_SndDeterminized;
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	private final ComplementDeterministicNwa<LETTER,STATE> m_SndComplemented;
	private final IntersectNwa<LETTER, STATE> m_Intersect;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;
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
			) throws OperationCanceledException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = m_FstOperand.getStateFactory();
		m_StateDeterminizer = new PowersetDeterminizer<LETTER,STATE>(sndOperand);
		s_Logger.info(startMessage());
		m_SndDeterminized = new DeterminizeNwa<LETTER,STATE>(m_SndOperand,m_StateDeterminizer,m_StateFactory);
		m_SndComplemented = new ComplementDeterministicNwa<LETTER, STATE>(m_SndDeterminized);
		m_Intersect = new IntersectNwa<LETTER, STATE>(m_FstOperand, m_SndComplemented, m_StateFactory, false);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Intersect);
		s_Logger.info(exitMessage());
	}
	
	public Difference(INestedWordAutomatonOldApi<LETTER,STATE> fstOperand,
			INestedWordAutomatonOldApi<LETTER,STATE> sndOperand,
			IStateDeterminizer<LETTER, STATE> stateDeterminizer,
			boolean nonFinalInSndIsTrap,
			StateFactory<STATE> sf
			) throws OperationCanceledException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = sf;
		m_StateDeterminizer = stateDeterminizer;
		s_Logger.info(startMessage());
		m_SndDeterminized = new DeterminizeNwa<LETTER,STATE>(m_SndOperand,m_StateDeterminizer,m_StateFactory);
		m_SndComplemented = new ComplementDeterministicNwa<LETTER, STATE>(m_SndDeterminized);
		m_Intersect = new IntersectNwa<LETTER, STATE>(m_FstOperand, m_SndComplemented, m_StateFactory, nonFinalInSndIsTrap);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Intersect);
		s_Logger.info(exitMessage());
	}
	






	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		assert (checkResult(m_StateFactory));
		return m_Result;
	}


	
	public boolean checkResult(StateFactory<STATE> sf) throws OperationCanceledException {
		s_Logger.info("Start testing correctness of " + operationName());
		INestedWordAutomatonOldApi<LETTER, STATE> fstOperandOldApi = ResultChecker.getOldApiNwa(m_FstOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> sndOperandOldApi = ResultChecker.getOldApiNwa(m_SndOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> resultDD = 
				(new DifferenceDD<LETTER, STATE>(fstOperandOldApi,sndOperandOldApi, 
						new PowersetDeterminizer<LETTER, STATE>(sndOperandOldApi),sf,false,false)).getResult();
		boolean correct = true;
		correct &= (resultDD.size() == m_Result.size());
		assert correct;
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
	
	
	
}

