package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class BuchiIntersect<LETTER,STATE> implements IOperation<LETTER,STATE> {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_FstOperand;
	private final INestedWordAutomatonSimple<LETTER,STATE> m_SndOperand;
	private BuchiIntersectNwa<LETTER, STATE> m_Intersect;
	private NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;
	private final StateFactory<STATE> m_StateFactory;
	
	
	@Override
	public String operationName() {
		return "buchiIntersect";
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
	
	
	
	
	public BuchiIntersect(INestedWordAutomatonSimple<LETTER,STATE> fstOperand,
			INestedWordAutomatonSimple<LETTER,STATE> sndOperand
			) throws AutomataLibraryException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = m_FstOperand.getStateFactory();
		doIntersect();
	}
	
	public BuchiIntersect(INestedWordAutomatonSimple<LETTER,STATE> fstOperand,
			INestedWordAutomatonSimple<LETTER,STATE> sndOperand,
			StateFactory<STATE> sf) throws AutomataLibraryException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = sf;
		doIntersect();
	}
	
	private void doIntersect() throws AutomataLibraryException {
		s_Logger.info(startMessage());
		m_Intersect = new BuchiIntersectNwa<LETTER, STATE>(m_FstOperand, m_SndOperand, m_StateFactory);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Intersect);
		s_Logger.info(exitMessage());
	}
	






	@Override
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult()
			throws OperationCanceledException {
		return m_Result;
	}


	
	public boolean checkResult(StateFactory<STATE> sf) throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		INestedWordAutomatonOldApi<LETTER, STATE> fstOperandOldApi = ResultChecker.getOldApiNwa(m_FstOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> sndOperandOldApi = ResultChecker.getOldApiNwa(m_SndOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> resultDD = (new BuchiIntersectDD<LETTER, STATE>(fstOperandOldApi,sndOperandOldApi)).getResult();
		boolean correct = true;
//		correct &= (resultDD.size() <= m_Result.size());
		assert correct;
		correct &= resultCheckWithRandomWords();
		assert correct;
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_FstOperand,m_SndOperand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	private boolean resultCheckWithRandomWords() throws OperationCanceledException {
		INestedWordAutomatonOldApi<LETTER, STATE> fstOperandOldApi = 
				ResultChecker.getOldApiNwa(m_FstOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> sndOperandOldApi = 
				ResultChecker.getOldApiNwa(m_SndOperand);
		List<NestedLassoWord<LETTER>> lassoWords = 
				new ArrayList<NestedLassoWord<LETTER>>();
		BuchiIsEmpty<LETTER, STATE> resultEmptiness = 
				new BuchiIsEmpty<LETTER, STATE>(m_Result);
		if (!resultEmptiness.getResult()) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		BuchiIsEmpty<LETTER, STATE> fstOperandEmptiness = 
				new BuchiIsEmpty<LETTER, STATE>(fstOperandOldApi);
		if (fstOperandEmptiness.getResult()) {
			assert resultEmptiness.getResult();
		} else 	{
			lassoWords.add(fstOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		BuchiIsEmpty<LETTER, STATE> sndOperandEmptiness = 
				new BuchiIsEmpty<LETTER, STATE>(fstOperandOldApi);
		if (sndOperandEmptiness.getResult()) {
			assert resultEmptiness.getResult();
		} else 	{
			lassoWords.add(sndOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, m_Result.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, fstOperandOldApi.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, sndOperandOldApi.size()));
		boolean correct = true;
		for (NestedLassoWord<LETTER> nlw : lassoWords) {
			correct &= checkAcceptance(nlw, fstOperandOldApi, sndOperandOldApi);
			assert correct;
		}
		return correct;
	}
	
	
	

	
	private boolean checkAcceptance(NestedLassoWord<LETTER> nlw,
			INestedWordAutomatonOldApi<LETTER, STATE> operand1,
			INestedWordAutomatonOldApi<LETTER, STATE> operand2) {
		boolean op1 = (new BuchiAccepts<LETTER, STATE>(operand1, nlw)).getResult();
		boolean op2 = (new BuchiAccepts<LETTER, STATE>(operand2, nlw)).getResult();
		boolean res = (new BuchiAccepts<LETTER, STATE>(m_Result, nlw)).getResult();
		return ((op1 && op2) == res);
	}
	
	
}

