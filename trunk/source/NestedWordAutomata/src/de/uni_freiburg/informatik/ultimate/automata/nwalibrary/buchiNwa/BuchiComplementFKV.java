package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
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

	

/**
 * Buchi Complementation based on 
 * 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiComplementFKV<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * TODO Allow definition of a maximal rank for cases where you know that
	 * this is sound. E.g. if the automaton is reverse deterministic a maximal
	 * rank of 2 is suffient, see paper of Seth Forgaty.
	 */
	final int m_UserDefinedMaxRank = Integer.MAX_VALUE;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Result;
	private final StateFactory<STATE> m_StateFactory;
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	private final BuchiComplementFKVNwa<LETTER, STATE> m_Complemented;	
	
	
	
	@Override
	public String operationName() {
		return "buchiComplementFKV";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand " + 
				m_Operand.sizeInformation() + " Result " + 
				m_Result.sizeInformation() + 
			"the highest rank that occured is " + m_Complemented.getHighesRank();
	}




	public BuchiComplementFKV(INestedWordAutomatonSimple<LETTER,STATE> input) throws OperationCanceledException {
		this.m_StateDeterminizer = new PowersetDeterminizer<LETTER, STATE>(input, true);
		this.m_StateFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.info(startMessage());
		m_Complemented = new BuchiComplementFKVNwa<LETTER, STATE>(input,m_StateDeterminizer,m_StateFactory);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Complemented);
		s_Logger.info(exitMessage());
	}
	
	public BuchiComplementFKV(INestedWordAutomatonSimple<LETTER,STATE> input, IStateDeterminizer<LETTER, STATE> stateDeterminizier) throws OperationCanceledException {
		this.m_StateDeterminizer = stateDeterminizier;
		this.m_StateFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.info(startMessage());
		m_Complemented = new BuchiComplementFKVNwa<LETTER, STATE>(input,m_StateDeterminizer,m_StateFactory);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Complemented);
		s_Logger.info(exitMessage());
	}
	
	
	
	


	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		boolean underApproximationOfComplement = false;
		boolean correct = true;
		s_Logger.info("Start testing correctness of " + operationName());
		INestedWordAutomatonOldApi<LETTER, STATE> operandOldApi = 
				ResultChecker.getOldApiNwa(m_Operand);
		List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<NestedLassoWord<LETTER>>();
		BuchiIsEmpty<LETTER, STATE> operandEmptiness = new BuchiIsEmpty<LETTER, STATE>(operandOldApi);
		boolean operandEmpty = operandEmptiness.getResult();
		if (!operandEmpty) {
			lassoWords.add(operandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		BuchiIsEmpty<LETTER, STATE> resultEmptiness = new BuchiIsEmpty<LETTER, STATE>(m_Result);
		boolean resultEmpty = resultEmptiness.getResult();
		if (!resultEmpty) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		correct &= !(operandEmpty && resultEmpty);
		assert correct;
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, m_Result.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, m_Result.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(operandOldApi)).getResult());
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(m_Result)).getResult());

		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		

		for (NestedLassoWord<LETTER> nlw : lassoWords) {
			boolean thistime = checkAcceptance(nlw, operandOldApi, underApproximationOfComplement);
			if (!thistime) {
				thistime = checkAcceptance(nlw, operandOldApi, underApproximationOfComplement);
			}
			correct &= thistime;
//			assert correct;
		}

		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_Operand);
			ResultChecker.writeToFileIfPreferred(operationName() + "FailedRes", "", m_Result);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	
	private boolean checkAcceptance(NestedLassoWord<LETTER> nlw,
			INestedWordAutomatonOldApi<LETTER, STATE> operand , 
			boolean underApproximationOfComplement) {
		boolean op = (new BuchiAccepts<LETTER, STATE>(operand, nlw)).getResult();
		boolean res = (new BuchiAccepts<LETTER, STATE>(m_Result, nlw)).getResult();
		boolean correct;
		if (underApproximationOfComplement) {
			correct = !res || op;
		} else {
			correct = op ^ res;
		}
//		assert correct : operationName() + " wrong result!";
		return correct;
	}


	@Override
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() throws OperationCanceledException {
		return m_Result;
	}
















}
