/**
 * TODO: Copyright.
 */
package de.uni_freiburg.informatik.ultimate.mso;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO: Comment.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public abstract class MSODAutomataOperations {

	/**
	 * Constructs an empty automaton.
	 */
	public NestedWordAutomaton<MSODAlphabetSymbol, String> emptyAutomaton(final AutomataLibraryServices services) {

		final Set<MSODAlphabetSymbol> alphabet = new HashSet<>();
		final VpAlphabet<MSODAlphabetSymbol> vpAlphabet = new VpAlphabet<>(alphabet);
		final StringFactory stringFactory = new StringFactory();

		return new NestedWordAutomaton<>(services, vpAlphabet, stringFactory);
	}

	/**
	 * Constructs an automaton that represents an Int variable.
	 *
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	public NestedWordAutomaton<MSODAlphabetSymbol, String> intVariableAutomaton(final AutomataLibraryServices services,
			final Term x) {

		if (!MSODUtils.isIntVariable(x)) {
			throw new IllegalArgumentException("Input x must be an Int variable.");
		}

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
	 * TODO: Check if there is any difference between Nat and Int.
	 *
	 * Constructs a copy of the given automaton with the extended or reduced alphabet.
	 */
	public NestedWordAutomaton<MSODAlphabetSymbol, String> reconstruct(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<MSODAlphabetSymbol> alphabet,
			final boolean isExtended) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> result;

		result = emptyAutomaton(services);
		result.getAlphabet().addAll(alphabet);

		for (final String state : automaton.getStates()) {
			result.addState(automaton.isInitial(state), automaton.isFinal(state), state);
		}

		for (final String state : automaton.getStates()) {

			for (final OutgoingInternalTransition<MSODAlphabetSymbol, String> transition : automaton
					.internalSuccessors(state)) {

				final Iterator<MSODAlphabetSymbol> itMatches =
						isExtended ? alphabet.stream().filter(e -> e.contains(transition.getLetter())).iterator()
								: alphabet.stream().filter(e -> transition.getLetter().contains(e)).iterator();

				while (itMatches.hasNext()) {
					result.addInternalTransition(state, itMatches.next(), transition.getSucc());
				}
			}
		}

		return result;
	}

	/**
	 * TODO: Comment.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Complement} or {@link Union} fails
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String> complement(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException;

	/**
	 * TODO Comment.
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> union(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new Union<>(services, new MSODStringFactory(), automaton1, automaton2).getResult();

		result = minimize(services, result);

		return result;
	}

	/**
	 * TODO: Comment.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Intersect} fails
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String> intersect(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException;

	/**
	 * TODO: Comment.
	 *
	 * @throws AutomataLibraryException
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> minimize(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		final INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new MinimizeSevpa<>(services, new MSODStringFactory(), automaton).getResult();

		return result;
	}

	/**
	 * Returns an automaton where also the given states are final.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if construction of {@link NestedWordAutomatonReachableStates} fails.
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> makeStatesFinal(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<String> states)
			throws AutomataLibraryException {

		NestedWordAutomatonReachableStates<MSODAlphabetSymbol, String> nwaReachableStates;
		nwaReachableStates = new NestedWordAutomatonReachableStates<>(services, automaton);

		final Set<String> finals = new HashSet<>(automaton.getFinalStates());
		finals.addAll(states);

		return new NestedWordAutomatonFilteredStates<>(services, nwaReachableStates, automaton.getStates(),
				automaton.getInitialStates(), finals);
	}

	/**
	 * TODO: Comment.
	 *
	 * @throws AutomataLibraryException
	 *             if {@link IsEmpty} fails
	 */
	public abstract Map<Term, Term> getResult(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException;

}
