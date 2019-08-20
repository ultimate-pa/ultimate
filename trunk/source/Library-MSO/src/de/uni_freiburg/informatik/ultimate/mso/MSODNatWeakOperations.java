/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO: Comment.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
@Deprecated
public final class MSODNatWeakOperations extends MSODNatOperationsBase {

	/**
	 * TODO Comment.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> complement(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new Complement<>(services, new MSODStringFactory(), automaton).getResult();

		result = minimize(services, result);

		if (result.getAlphabet().isEmpty()) {
			return result;
		}

		// Find all Int variables contained in the alphabet.
		final Set<Term> intVars = new HashSet<>(result.getAlphabet().iterator().next().getMap().keySet());
		intVars.removeIf(o -> !MSODUtils.isIntVariable(o));

		// Intersect with an automaton that ensures that each Int variable is matched to exactly one value.
		for (final Term intVar : intVars) {
			INestedWordAutomaton<MSODAlphabetSymbol, String> varAutomaton;
			varAutomaton = intVariableAutomaton(services, intVar);
			varAutomaton = reconstruct(services, varAutomaton, result.getAlphabet(), true);

			result = intersect(services, result, varAutomaton);
		}

		return result;
	}

	/**
	 * TODO Comment.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> intersect(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new Intersect<>(services, new MSODStringFactory(), automaton1, automaton2).getResult();

		result = minimize(services, result);

		return result;
	}

	/**
	 * TODO Comment.
	 *
	 * @throws AutomataOperationCanceledException
	 */
	public NestedWord<MSODAlphabetSymbol> getWord(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		NestedWord<MSODAlphabetSymbol> result = null;

		final IsEmpty<MSODAlphabetSymbol, String> isEmpty = new IsEmpty<>(services, automaton);

		if (!isEmpty.getResult()) {
			final NestedRun<MSODAlphabetSymbol, String> run = isEmpty.getNestedRun();
			result = run.getWord();

			// throw new IllegalArgumentException("RUN: '" + run.toString() + "'");
		}

		return result;
	}

	/**
	 * TODO Comment.
	 *
	 * @throws AutomataOperationCanceledException
	 */
	@Override
	public Map<Term, Term> getResult(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		Map<Term, Term> result = new HashMap<>();
		final NestedWord<MSODAlphabetSymbol> word = getWord(script, services, automaton);

		if (word != null) {
			result = MSODUtils.parseMSODNatToTerm(script, word);
		}

		return result;
	}

}
