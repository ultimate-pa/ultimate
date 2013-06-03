package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
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
	private final PowersetDeterminizer<LETTER, STATE> stateDeterminizer;
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
		return "Finished " + operationName() + " Result " + 
				m_Result.sizeInformation() + 
			"the highest rank that occured is " + m_Complemented.getHighesRank();
	}




	public BuchiComplementFKV(INestedWordAutomatonSimple<LETTER,STATE> input) throws OperationCanceledException {
		this.stateDeterminizer = new PowersetDeterminizer<LETTER, STATE>(input);
		this.m_StateFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.info(startMessage());
		m_Complemented = new BuchiComplementFKVNwa<LETTER, STATE>(input,stateDeterminizer,m_StateFactory);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Complemented);
		s_Logger.info(exitMessage());
	}
	
	
	
	


	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return (ResultChecker.buchiComplement(ResultChecker.getOldApiNwa(m_Operand), m_Result));
	}


	@Override
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() throws OperationCanceledException {
		return m_Result;
	}
















}
