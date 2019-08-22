/**
 * TODO: Copyright.
 */
package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO: Comment.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODAutomataOperationsBuchi extends MSODAutomataOperations {

	/**
	 * TODO Comment.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> complement(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new BuchiComplementFKV<>(services, new MSODStringFactory(), automaton).getResult();

		result = minimize(services, result);

		if (result.getAlphabet().isEmpty()) {
			return result;
		}

		// Find all Int variables contained in the alphabet.
		final Set<Term> intVars = result.getAlphabet().iterator().next().containsSort(SmtSortUtils.INT_SORT);

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
				new BuchiIntersect<>(services, new MSODStringFactory(), automaton1, automaton2).getResult();

		result = minimize(services, result);

		return result;
	}

	/**
	 * TODO Comment.
	 *
	 * @throws AutomataLibraryException
	 *             if {@link BuchiIsEmpty} fails
	 */
	public NestedLassoWord<MSODAlphabetSymbol> getWord(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		NestedLassoWord<MSODAlphabetSymbol> result = null;

		final BuchiIsEmpty<MSODAlphabetSymbol, String> isEmpty = new BuchiIsEmpty<>(services, automaton);

		if (!isEmpty.getResult()) {
			final NestedLassoRun<MSODAlphabetSymbol, String> run = isEmpty.getAcceptingNestedLassoRun();
			result = run.getNestedLassoWord();

			// throw new IllegalArgumentException(result.toString());
		}

		return result;
	}

	/**
	 * TODO Comment.
	 *
	 * @throws AutomataOperationCanceledException
	 */
	// @Override
	// public Map<Term, Term> getResult(final Script script, final AutomataLibraryServices services,
	// final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
	//
	// Map<Term, Term> result = new HashMap<>();
	// final NestedLassoWord<MSODAlphabetSymbol> word = getWord(script, services, automaton);
	//
	// if (word != null) {
	// final NestedWord<MSODAlphabetSymbol> stem = word.getStem();
	// final NestedWord<MSODAlphabetSymbol> loop = word.getLoop();
	//
	// result = MSODUtils.parseMSODNatToTerm(script, stem);
	// }
	//
	// return result;
	// }

	/**
	 * TODO Comment.
	 *
	 * @throws AutomataOperationCanceledException
	 */
	@Override
	public Map<Term, Term> getResult(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		final Map<Term, Term> result = new HashMap<>();
		final NestedLassoWord<MSODAlphabetSymbol> word = getWord(script, services, automaton);

		if (word != null) {
			final NestedWord<MSODAlphabetSymbol> stem = word.getStem();
			final NestedWord<MSODAlphabetSymbol> loop = word.getLoop();

			if (automaton.getAlphabet().isEmpty()) {
				// TODO: Deal with empty alphabet.
			}

			final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();

			// Collect all stem indices at which the value is 1.
			final Map<Term, Set<Integer>> stemIndices = new HashMap<>();

			for (final Term term : terms) {
				stemIndices.put(term, new HashSet<>());
			}

			for (int i = 0; i < stem.length(); i++) {
				final MSODAlphabetSymbol symbol = stem.getSymbol(i);
				for (final Entry<Term, Boolean> entry : symbol.getMap().entrySet()) {
					if (entry.getValue()) {
						stemIndices.get(entry.getKey()).add(i);
					}
				}
			}

			// Collect all loop indices at which the value is 1.
			final Map<Term, Set<Integer>> loopIndices = new HashMap<>();

			for (final Term term : terms) {
				loopIndices.put(term, new HashSet<>());
			}

			for (int i = 0; i < loop.length(); i++) {
				final MSODAlphabetSymbol symbol = loop.getSymbol(i);
				for (final Entry<Term, Boolean> entry : symbol.getMap().entrySet()) {
					if (entry.getValue()) {
						loopIndices.get(entry.getKey()).add(i);
					}
				}
			}

			// TODO: Construct result term.
			for (final Term term : terms) {
				Term stemTerm = null;
				Term loopTerm = null;

				// Deal with variables of type Int.
				if (SmtSortUtils.isIntSort(term.getSort())) {
					if (stemIndices.get(term).size() != 1 || loopIndices.get(term).size() != 0) {
						throw new IllegalArgumentException("This is not a valid Integer representation!");
					}
					final Term value = SmtUtils.constructIntValue(script,
							BigInteger.valueOf(stemIndices.get(term).iterator().next()));
					result.put(term, value);
					// Deal with variables of other type.
				} else {
					final Term newSetTerm = script.variable(term.toString() + "_elem", SmtSortUtils.getIntSort(script));
					Term resultTerm = null;
					final Iterator<Integer> itStem = stemIndices.get(term).iterator();
					final Iterator<Integer> itLoop = loopIndices.get(term).iterator();

					while (itStem.hasNext()) {
						final Term value = SmtUtils.constructIntValue(script, BigInteger.valueOf(itStem.next()));
						final Term eqTerm = SmtUtils.binaryEquality(script, newSetTerm, value);
						if (stemTerm == null) {
							stemTerm = eqTerm;
						}
						stemTerm = SmtUtils.or(script, eqTerm, stemTerm);
					}

					final int lastStemIndex = Collections.max(stemIndices.get(term));
					final int lastLoopIndex = Collections.max(loopIndices.get(term));

					// exclude numbers already occurring in the stem
					final Term t1 = SmtUtils.minus(script, newSetTerm,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(lastStemIndex)));
					final Term t2 = SmtUtils.greater(script, t1, SmtUtils.constructIntValue(script, BigInteger.ZERO));
					final Term t3 = SmtUtils.mod(script, t1,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(lastLoopIndex + 1)));
					while (itLoop.hasNext()) {
						loopTerm = SmtUtils.and(script, t2,
								SmtUtils.binaryEquality(script, t3, SmtUtils.constructIntValue(script,
										BigInteger.valueOf((itLoop.next() + 1) % (lastLoopIndex + 1)))));

					}
					resultTerm = SmtUtils.or(script, stemTerm, loopTerm);

					result.put(term, resultTerm);
				}
			}

		}
		return result;
	}

}
