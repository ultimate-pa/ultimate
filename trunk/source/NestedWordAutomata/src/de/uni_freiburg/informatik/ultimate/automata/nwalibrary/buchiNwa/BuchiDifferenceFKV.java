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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class BuchiDifferenceFKV<LETTER,STATE> implements IOperation<LETTER,STATE> {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_FstOperand;
	private final INestedWordAutomatonSimple<LETTER,STATE> m_SndOperand;
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	private BuchiComplementFKVNwa<LETTER,STATE> m_SndComplemented;
	private BuchiIntersectNwa<LETTER, STATE> m_Intersect;
	private NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;
	private final StateFactory<STATE> m_StateFactory;
	
	
	@Override
	public String operationName() {
		return "buchiDifferenceFKV";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". First operand " + 
				m_FstOperand.sizeInformation() + ". Second operand " + 
				m_SndOperand.sizeInformation();	
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". First operand " + 
				m_FstOperand.sizeInformation() + ". Second operand " + 
				m_SndOperand.sizeInformation() + " Result " + 
				m_Result.sizeInformation() + 
			"the highest rank that occured is " + m_SndComplemented.getHighesRank();
	}
	
	
	
	
	public BuchiDifferenceFKV(INestedWordAutomatonSimple<LETTER,STATE> fstOperand,
			INestedWordAutomatonSimple<LETTER,STATE> sndOperand
			) throws AutomataLibraryException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = m_FstOperand.getStateFactory();
		m_StateDeterminizer = new PowersetDeterminizer<LETTER,STATE>(sndOperand, true);
		s_Logger.info(startMessage());
		computateDifference();
		s_Logger.info(exitMessage());
	}
	
	
	public BuchiDifferenceFKV(INestedWordAutomatonSimple<LETTER,STATE> fstOperand,
			INestedWordAutomatonSimple<LETTER,STATE> sndOperand,
			IStateDeterminizer<LETTER, STATE> stateDeterminizer,
			StateFactory<STATE> sf) throws AutomataLibraryException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = sf;
		m_StateDeterminizer = stateDeterminizer;
		s_Logger.info(startMessage());
		computateDifference();
		s_Logger.info(exitMessage());
	}
	
	private void computateDifference() throws AutomataLibraryException {
		m_SndComplemented = new BuchiComplementFKVNwa<LETTER, STATE>(m_SndOperand, m_StateDeterminizer, m_StateFactory);
		m_Intersect = new BuchiIntersectNwa<LETTER, STATE>(m_FstOperand, m_SndComplemented, m_StateFactory);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Intersect);
	}
	






	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		boolean underApproximationOfComplement = false;
		boolean correct = true;
			s_Logger.info("Start testing correctness of " + operationName());
			INestedWordAutomatonOldApi<LETTER, STATE> fstOperandOldApi = ResultChecker.getOldApiNwa(m_FstOperand);
			INestedWordAutomatonOldApi<LETTER, STATE> sndOperandOldApi = ResultChecker.getOldApiNwa(m_SndOperand);
			List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<NestedLassoWord<LETTER>>();
			BuchiIsEmpty<LETTER, STATE> fstOperandEmptiness = new BuchiIsEmpty<LETTER, STATE>(fstOperandOldApi);
			boolean fstOperandEmpty = fstOperandEmptiness.getResult();
			if (!fstOperandEmpty) {
				lassoWords.add(fstOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
			}
			BuchiIsEmpty<LETTER, STATE> sndOperandEmptiness = new BuchiIsEmpty<LETTER, STATE>(fstOperandOldApi);
			boolean sndOperandEmpty = sndOperandEmptiness.getResult();
			if (!sndOperandEmpty) {
				lassoWords.add(sndOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
			}
			BuchiIsEmpty<LETTER, STATE> resultEmptiness = new BuchiIsEmpty<LETTER, STATE>(m_Result);
			boolean resultEmpty = resultEmptiness.getResult();
			if (!resultEmpty) {
				lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
			}
			correct &= (!fstOperandEmpty || resultEmpty);
			assert correct;
			lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, m_Result.size()));
			lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, fstOperandOldApi.size()));
			lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, sndOperandOldApi.size()));

			for (NestedLassoWord<LETTER> nlw : lassoWords) {
				correct &= checkAcceptance(nlw, fstOperandOldApi, sndOperandOldApi, underApproximationOfComplement);
				assert correct;
			}
			if (!correct) {
				ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_FstOperand,m_SndOperand);
			}
			s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	private boolean checkAcceptance(NestedLassoWord<LETTER> nlw,
			INestedWordAutomatonOldApi<LETTER, STATE> operand1, 
			INestedWordAutomatonOldApi<LETTER, STATE> operand2,
			boolean underApproximationOfComplement) {
		boolean correct;
		boolean op1 = (new BuchiAccepts<LETTER, STATE>(operand1, nlw)).getResult();
		boolean op2 = (new BuchiAccepts<LETTER, STATE>(operand2, nlw)).getResult();
		boolean res = (new BuchiAccepts<LETTER, STATE>(m_Result, nlw)).getResult();
		if (res) {
			correct = op1 && !op2;
		} else {
			correct = !(!underApproximationOfComplement && op1 && !op2);
		}
		assert correct : operationName() + " wrong result!";
		return correct;
	}

}
