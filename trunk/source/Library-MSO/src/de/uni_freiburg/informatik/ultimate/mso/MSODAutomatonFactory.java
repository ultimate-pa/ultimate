package de.uni_freiburg.informatik.ultimate.mso;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class MSODAutomatonFactory {

	/**
	 * Constructs an empty automaton.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> emptyAutomaton(
			final AutomataLibraryServices services) {

		final Set<MSODAlphabetSymbol> alphabet = new HashSet<MSODAlphabetSymbol>();
		final VpAlphabet<MSODAlphabetSymbol> vpAlphabet = new VpAlphabet<MSODAlphabetSymbol>(alphabet);
		final StringFactory stringFactory = new StringFactory();

		return new NestedWordAutomaton<MSODAlphabetSymbol, String>(services, vpAlphabet, stringFactory);
	}

	/**
	 * Constructs an automaton that represents "false".
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> falseAutomaton(
			final AutomataLibraryServices services) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, false, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "true".
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> trueAutomaton(
			final AutomataLibraryServices services) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, true, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents an Int variable.
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> intVariableAutomaton(
			final AutomataLibraryServices services, final Term x) {

		if (!MSODUtils.isIntVariable(x))
			throw new IllegalArgumentException("Input x must be an Int variable.");

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbols = MSODUtils.createAlphabet(x);
		automaton.getAlphabet().addAll(symbols.values());

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");

		automaton.addInternalTransition("init", symbols.get("x0"), "init");
		automaton.addInternalTransition("init", symbols.get("x1"), "final");
		automaton.addInternalTransition("final", symbols.get("x0"), "final");

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} which is constructed from the given
	 * {@link INestedWordAutomaton}.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> nwa(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> result = emptyAutomaton(services);
		result.getAlphabet().addAll(automaton.getAlphabet());

		for (final String state : automaton.getStates())
			result.addState(automaton.isInitial(state), automaton.isFinal(state), state);

		for (final String state : automaton.getStates()) {
			for (final OutgoingInternalTransition<MSODAlphabetSymbol, String> transition : automaton
					.internalSuccessors(state))
				result.addInternalTransition(state, transition.getLetter(), transition.getSucc());
		}

		return result;
	}


	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
}