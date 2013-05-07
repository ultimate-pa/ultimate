package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * Operation that checks if the language of the first Buchi automaton is 
 * included in the language of the second Buchi automaton.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <LETTER>
 * @param <STATE>
 */
public class BuchiIsIncluded<LETTER, STATE> implements IOperation {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	private final INestedWordAutomaton<LETTER, STATE> m_Operand1;
	private final INestedWordAutomaton<LETTER, STATE> m_Operand2;

	private final Boolean m_Result;

	private final NestedLassoRun<LETTER, STATE> m_Counterexample;

	public BuchiIsIncluded(INestedWordAutomaton<LETTER, STATE> nwa1,
			INestedWordAutomaton<LETTER, STATE> nwa2)
			throws OperationCanceledException {
		m_Operand1 = nwa1;
		m_Operand2 = nwa2;
		s_Logger.info(startMessage());

		INestedWordAutomaton<LETTER, STATE> sndComplement = (new BuchiComplementFKV<LETTER, STATE>(
				m_Operand2)).getResult();
		INestedWordAutomaton<LETTER, STATE> difference = (new BuchiIntersect<LETTER, STATE>(
				m_Operand1, sndComplement, true)).getResult();
		BuchiIsEmpty<LETTER, STATE> emptinessCheck = new BuchiIsEmpty<LETTER, STATE>(
				(INestedWordAutomaton<LETTER, STATE>) difference);

		m_Result = emptinessCheck.getResult();
		m_Counterexample = emptinessCheck.getAcceptingNestedLassoRun();
		s_Logger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "isIncluded";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand1 "
				+ m_Operand1.sizeInformation() + ". Operand2 "
				+ m_Operand2.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Language is "
				+ (m_Result ? "" : "not ") + "included";
	}

	@Override
	public Boolean getResult() throws OperationCanceledException {
		return m_Result;
	}

	public NestedLassoRun<LETTER, STATE> getCounterexample() {
		return m_Counterexample;
	}

}
