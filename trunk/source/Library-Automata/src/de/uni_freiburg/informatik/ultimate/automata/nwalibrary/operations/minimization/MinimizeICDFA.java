package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.text.MessageFormat;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeDfaHopcroft.Partition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * Utility class for minimizing ICDFAs (Incomplete Deterministic Finite
 * Automaton). Uses a modification of the Hopcroft algorithm.<br/>
 * Runtime is in:<br/>
 * <b>O(m * log(n))</b> with usage of<br/>
 * <b>O(k + n + m)</b> space<br/>
 * where 'n' is the number of states, 'm' the number of edges and 'k' the size
 * of the alphabet.
 * 
 * @author Daniel Tischner
 *
 */
@SuppressWarnings("deprecation")
public final class MinimizeICDFA implements IOperation<String, String> {

	/**
	 * Logger for debug information.
	 */
	private static Logger s_Logger = NestedWordAutomata.getLogger();
	/**
	 * Input automaton that should be minimized.
	 */
	private final INestedWordAutomaton<String, String> m_operand;
	/**
	 * Resulting minimized automaton.
	 */
	private final NestedWordAutomaton<String, String> m_result;
	/**
	 * Service provider.
	 */
	private final IUltimateServiceProvider m_Services;

	/**
	 * Minimizes a given ICDFA (Incomplete Deterministic Finite Automaton).<br/>
	 * Runtime is in:<br/>
	 * <b>O(m * log(n))</b> with usage of<br/>
	 * <b>O(k + n + m)</b> space<br/>
	 * where 'n' is the number of states, 'm' the number of edges and 'k' the
	 * size of the alphabet.
	 * 
	 * @param services
	 *            Service provider
	 * @param operand
	 *            Automaton to minimize
	 */
	public MinimizeICDFA(final IUltimateServiceProvider services,
			final INestedWordAutomaton<String, String> operand) {
		m_Services = services;
		m_operand = operand;
		m_result = minimizeICDFA(m_operand);
	}

	@Override
	public boolean checkResult(StateFactory<String> stateFactory)
			throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		boolean correct = true;
		// TODO Use OldApi or convert it from new.
		/*
		 * correct &= (ResultChecker.nwaLanguageInclusion(m_Services, m_operand,
		 * m_result, stateFactory) == null); correct &=
		 * (ResultChecker.nwaLanguageInclusion(m_Services, m_result, m_operand,
		 * stateFactory) == null); if (!correct) {
		 * ResultChecker.writeToFileIfPreferred(m_Services, operationName() +
		 * "Failed", "", m_operand); }
		 */
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_result.sizeInformation() + ".";
	}

	@Override
	public Object getResult() throws AutomataLibraryException {
		return m_result;
	}

	/**
	 * Minimizes a given ICDFA (Incomplete Deterministic Finite Automaton).<br/>
	 * Runtime is in:<br/>
	 * <b>O(m * log(n))</b> with usage of<br/>
	 * <b>O(k + n + m)</b> space<br/>
	 * where 'n' is the number of states, 'm' the number of edges and 'k' the
	 * size of the alphabet.
	 * 
	 * @param icdfa
	 *            Automaton to minimize
	 * @return Minimized automaton
	 */
	private NestedWordAutomaton<String, String> minimizeICDFA(
			final INestedWordAutomaton<String, String> icdfa) {
		// TODO Implementation
		
		return null;
	}

	@Override
	public String operationName() {
		return "MinimizeICDFA";
	}

	@Override
	public String startMessage() {
		return MessageFormat.format("Start {0}.", operationName());
	}
}