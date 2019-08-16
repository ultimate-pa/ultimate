/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO: Comment.
 *
 * TODO: Check inputs.
 *
 * TODO: Find meaningful names for the automata representing only one case of the complete automaton.
 *
 * TODO: Test all (new) Int automata.
 *
 * TODO: Note: Some methods are redundant to the ones in MoNatDiffAutomatonFactory (even though some are shortened by
 * the use of createAlphabet) including: emptyAutomaton, trueAutomaton, falseAutomaton, intVariableAutomaton,
 * reconstruct, createAlphabet, strictSubsetAutomaton, nonStrictSubsetAutomaton
 *
 * TODO: nonStrictSubset changed such that actually no transition is needed to be accepting.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODIntOperations extends MSODIntOperationsBase {

	/**
	 * TODO Comment.
	 *
	 * @throws AutomataOperationCanceledException
	 */
	public NestedLassoWord<MSODAlphabetSymbol> getWord(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		NestedLassoWord<MSODAlphabetSymbol> result = null;

		final BuchiIsEmpty<MSODAlphabetSymbol, String> isEmpty = new BuchiIsEmpty<>(services, automaton);

		if (!isEmpty.getResult()) {
			final NestedLassoRun<MSODAlphabetSymbol, String> run = isEmpty.getAcceptingNestedLassoRun();
			result = run.getNestedLassoWord();
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
		final NestedLassoWord<MSODAlphabetSymbol> word = getWord(script, services, automaton);

		if (word != null) {
			final NestedWord<MSODAlphabetSymbol> stem = word.getStem();
			final NestedWord<MSODAlphabetSymbol> loop = word.getLoop();

			final Term[] terms = automaton.getAlphabet().iterator().next().getTerms();
			result = MSODUtils.parseMSODIntToTerm(script, stem, terms);
		}

		return result;
	}
}
