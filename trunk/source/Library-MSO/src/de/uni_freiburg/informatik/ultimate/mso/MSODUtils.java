/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * TODO: Comment.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public final class MSODUtils {

	public static final String SET_OF_INT_SORT = "SetOfInt";

	/**
	 * TODO: Comment.
	 */
	public static Sort getSetOfIntSort(final Script script) {
		return script.sort(SET_OF_INT_SORT);
	}
	
	/**
	 * TODO: Comment.
	 */
	public static Sort getSetOfIntSort(final ManagedScript script) {
		return getSetOfIntSort(script.getScript());
	}

	/**
	 * Returns a set of integer constant that respects the UltimateNormalForm. See
	 * {@link UltimateNormalFormUtils}.
	 */
	public static Term constructSetOfIntValue(final Script script, final Set<BigInteger> numbers) {
		final Set<Term> terms = new HashSet<>();

		for (final BigInteger number : numbers) {
			terms.add(SmtUtils.constructIntValue(script, number));
		}

		return MSODUtils.getSetOfIntSort(script).getTheory().constant(terms,
				MSODUtils.getSetOfIntSort(script));
	}

	/**
	 * Returns true if sort is SetOfInt.
	 */
	public static boolean isSetOfIntSort(final Sort sort) {
		return sort.getName().equals(SET_OF_INT_SORT);
	}

	/**
	 * Returns true if term is an Int constant.
	 */
	public static boolean isIntConstant(final Term term) {
		return term instanceof ConstantTerm && SmtSortUtils.isIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a free Int variable.
	 */
	public static boolean isFreeIntVariable(final Term term) {
		return SmtUtils.isConstant(term) && SmtSortUtils.isIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a free SetOfInt variable.
	 */
	public static boolean isFreeSetOfIntVariable(final Term term) {
		return SmtUtils.isConstant(term) && isSetOfIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a quantified Int variable.
	 */
	public static boolean isQuantifiedIntVariable(final Term term) {
		return term instanceof TermVariable && SmtSortUtils.isIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a quantified SetOfInt variable.
	 */
	public static boolean isQuantifiedSetOfIntVariable(final Term term) {
		return term instanceof TermVariable && isSetOfIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a free variable.
	 */
	public static boolean isFreeVariable(final Term term) {
		return isFreeIntVariable(term) || isFreeSetOfIntVariable(term);
	}

	/**
	 * Returns true if term is a quantified variable.
	 */
	public static boolean isQuantifiedVariable(final Term term) {
		return isQuantifiedIntVariable(term) || isQuantifiedSetOfIntVariable(term);
	}

	/**
	 * Returns true if term is a variable.
	 */
	public static boolean isVariable(final Term term) {
		return isFreeVariable(term) || isQuantifiedVariable(term);
	}

	/**
	 * Returns true if term is an Int variable.
	 */
	public static boolean isIntVariable(final Term term) {
		return isFreeIntVariable(term) || isQuantifiedIntVariable(term);
	}

	/**
	 * Returns true if term is a SetOfInt variable.
	 */
	public static boolean isSetOfIntVariable(final Term term) {
		return isFreeSetOfIntVariable(term) || isQuantifiedSetOfIntVariable(term);
	}

	/**
	 * Returns the alphabet for the given variable names.
	 *
	 * TODO: Check input.
	 */
	public static Set<MSODAlphabetSymbol> createAlphabet(final Term[] terms) {
		final Set<MSODAlphabetSymbol> symbols = new HashSet<>();

		if (terms.length == 0) {
			symbols.add(new MSODAlphabetSymbol());
			return symbols;
		}

		for (int i = 0; i < Math.pow(2, terms.length); i++) {
			final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();

			for (int j = 0; j < terms.length; j++) {
				final int value = (i / (int) Math.pow(2, j)) % 2;
				symbol.add(terms[j], value == 1);
			}
			symbols.add(symbol);
		}

		return symbols;
	}

	/**
	 * Returns the alphabet for the given variable names. Alphabet symbols are
	 * mapped to its string representation.
	 */
	public static Map<String, MSODAlphabetSymbol> createAlphabet(final Term term) {
		final Map<String, MSODAlphabetSymbol> symbols = new HashMap<String, MSODAlphabetSymbol>();

		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(term, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(term, true);

		symbols.put("x0", x0);
		symbols.put("x1", x1);

		return symbols;
	}

	/**
	 * Returns the alphabet for the given variable names. Alphabet symbols are
	 * mapped to its string representation.
	 */
	public static Map<String, MSODAlphabetSymbol> createAlphabet(final Term term1, final Term term2) {
		final Map<String, MSODAlphabetSymbol> symbols = new HashMap<String, MSODAlphabetSymbol>();

		final Term[] terms = { term1, term2 };
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(terms, new boolean[] { false, false });
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(terms, new boolean[] { false, true });
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(terms, new boolean[] { true, false });
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(terms, new boolean[] { true, true });

		symbols.put("xy00", xy00);
		symbols.put("xy01", xy01);
		symbols.put("xy10", xy10);
		symbols.put("xy11", xy11);

		return symbols;
	}

	/**
	 * Returns the merged alphabet for given inputs.
	 */
	public static Set<MSODAlphabetSymbol> mergeAlphabets(final Set<MSODAlphabetSymbol> s1,
			final Set<MSODAlphabetSymbol> s2) {

		final Set<Term> terms = new HashSet<>();

		if (!s1.isEmpty()) {
			terms.addAll(s1.iterator().next().getMap().keySet());
		}

		if (!s2.isEmpty()) {
			terms.addAll(s2.iterator().next().getMap().keySet());
		}

		return createAlphabet(terms.toArray(new Term[terms.size()]));
	}

	/**
	 * Returns the alphabet symbols where all but the excluded variables match the
	 * given value.
	 */
	public static Set<MSODAlphabetSymbol> allMatchesAlphabet(final Set<MSODAlphabetSymbol> symbols, final Boolean value,
			final Term... excludedTerms) {

		final Set<MSODAlphabetSymbol> matches = new HashSet<>();

		for (final MSODAlphabetSymbol symbol : symbols) {
			if (symbol.allMatches(value, excludedTerms)) {
				matches.add(symbol);
			}
		}

		return matches;
	}

	/**
	 * Returns the successors which are directly reachable with the given symbols
	 * from the given state in the given automaton.
	 */
	public static Set<String> hierarchicalSuccessorsOutgoing(
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final String state,
			final Set<MSODAlphabetSymbol> symbols) {

		final Set<String> successors = new HashSet<>();
		for (final MSODAlphabetSymbol symbol : symbols) {

			for (final OutgoingInternalTransition<MSODAlphabetSymbol, String> transition : automaton
					.internalSuccessors(state, symbol)) {

				successors.add(transition.getSucc());
			}
		}

		return successors;
	}

	/**
	 * Returns the predecessors which are directly reachable with the given symbols
	 * from the given state in the given automaton.
	 */
	public static Set<String> hierarchicalPredecessorsIncoming(
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final String state,
			final Set<MSODAlphabetSymbol> symbols) {

		final Set<String> predecessors = new HashSet<>();
		for (final MSODAlphabetSymbol symbol : symbols) {

			for (final IncomingInternalTransition<MSODAlphabetSymbol, String> transition : automaton
					.internalPredecessors(state, symbol)) {

				predecessors.add(transition.getPred());
			}
		}

		return predecessors;
	}

	/**
	 * Returns a map which holds all terms and their values parsed from given word.
	 */
	public static Map<Term, Term> parseMoNatDiffToTerm(final Script script, final Word<MSODAlphabetSymbol> word,
			final Term... terms) {

		final Map<Term, Term> result = new HashMap<>();
		final Map<Term, Set<BigInteger>> values = new HashMap<>();

		for (final Term term : terms) {
			values.put(term, new HashSet<BigInteger>());
		}

		for (int i = 0; i < word.length(); i++) {
			final MSODAlphabetSymbol symbol = word.getSymbol(i);

			for (final Term term : terms) {
				if (symbol.getMap().get(term)) {
					values.get(term).add(BigInteger.valueOf(i));
				}
			}
		}

		for (final Term term : values.keySet()) {
			if (SmtSortUtils.isIntSort(term.getSort())) {
				assert (values.get(term) != null && values.get(term).size() == 1);

				final BigInteger value = values.get(term) != null ? values.get(term).iterator().next()
						: BigInteger.ZERO;
				result.put(term, SmtUtils.constructIntValue(script, value));
			}

			if (MSODUtils.isSetOfIntSort(term.getSort())) {
				result.put(term, MSODUtils.constructSetOfIntValue(script, values.get(term)));
			}
		}

		return result;
	}

	/**
	 * TODO:
	 */
	public static Map<Term, Term> parseMSODiffIntToTerm(final Script script, final Word<MSODAlphabetSymbol> word,
			final Term... terms) {

		final Map<Term, Term> result = new HashMap<>();
		final Map<Term, Set<BigInteger>> values = new HashMap<>();

		for (final Term term : terms) {
			values.put(term, new HashSet<BigInteger>());
		}

		for (int i = 0; i < word.length(); i++) {
			final MSODAlphabetSymbol symbol = word.getSymbol(i);

			for (final Term term : terms) {
				if (symbol.getMap().get(term)) {
					if (i % 2 == 0)
						values.get(term).add(BigInteger.valueOf(-i / 2));
					else {
						values.get(term).add(BigInteger.valueOf((i + 1) / 2));
					}
				}
			}
		}

		for (final Term term : values.keySet()) {
			if (SmtSortUtils.isIntSort(term.getSort())) {
				assert (values.get(term) != null && values.get(term).size() == 1);

				final BigInteger value = values.get(term) != null ? values.get(term).iterator().next()
						: BigInteger.ZERO;
				result.put(term, SmtUtils.constructIntValue(script, value));
			}

			if (MSODUtils.isSetOfIntSort(term.getSort())) {
				result.put(term, MSODUtils.constructSetOfIntValue(script, values.get(term)));
			}
		}

		return result;
	}
}