/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public final class MoNatDiffUtils {

	/**
	 * Returns true if sort is SetOfInt.
	 */
	public static boolean isSetOfIntSort(final Sort sort) {
		return sort.getName().equals("SetOfInt");
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
	public static Set<MoNatDiffAlphabetSymbol> createAlphabet(final Term[] terms) {
		final Set<MoNatDiffAlphabetSymbol> symbols = new HashSet<MoNatDiffAlphabetSymbol>();

		if (terms.length == 0) {
			symbols.add(new MoNatDiffAlphabetSymbol());
			return symbols;
		}

		for (int i = 0; i < Math.pow(2, terms.length); i++) {
			final MoNatDiffAlphabetSymbol symbol = new MoNatDiffAlphabetSymbol();

			for (int j = 0; j < terms.length; j++) {
				final int value = (i / (int) Math.pow(2, j)) % 2;
				symbol.add(terms[j], value == 1);
			}
			symbols.add(symbol);
		}

		return symbols;
	}

	/**
	 * Returns the merged alphabet for given inputs.
	 */
	public static Set<MoNatDiffAlphabetSymbol> mergeAlphabets(final Set<MoNatDiffAlphabetSymbol> s1,
			final Set<MoNatDiffAlphabetSymbol> s2) {

		final Set<Term> terms = new HashSet<Term>();

		if (!s1.isEmpty())
			terms.addAll(s1.iterator().next().getMap().keySet());

		if (!s2.isEmpty())
			terms.addAll(s2.iterator().next().getMap().keySet());

		return createAlphabet(terms.toArray(new Term[terms.size()]));
	}

	/**
	 * Returns the alphabet symbols where all but the excluded variables match the
	 * given value.
	 */
	public static Set<MoNatDiffAlphabetSymbol> allMatchesAlphabet(final Set<MoNatDiffAlphabetSymbol> symbols,
			final Boolean value, final Term... excludedTerms) {

		final Set<MoNatDiffAlphabetSymbol> matches = new HashSet<MoNatDiffAlphabetSymbol>();

		for (final MoNatDiffAlphabetSymbol symbol : symbols) {
			if (symbol.allMatches(value, excludedTerms))
				matches.add(symbol);
		}

		return matches;
	}

	/**
	 * Returns the successors which are directly reachable with the given symbols
	 * from the given state in the given automaton.
	 */
	public static Set<String> hierarchicalSuccessorsOutgoing(
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, final String state,
			final Set<MoNatDiffAlphabetSymbol> symbols) {

		final Set<String> successors = new HashSet<String>();
		for (final MoNatDiffAlphabetSymbol symbol : symbols) {

			for (final OutgoingInternalTransition<MoNatDiffAlphabetSymbol, String> transition : automaton
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
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, final String state,
			final Set<MoNatDiffAlphabetSymbol> symbols) {

		final Set<String> predecessors = new HashSet<String>();
		for (final MoNatDiffAlphabetSymbol symbol : symbols) {

			for (final IncomingInternalTransition<MoNatDiffAlphabetSymbol, String> transition : automaton
					.internalPredecessors(state, symbol)) {

				predecessors.add(transition.getPred());
			}
		}

		return predecessors;
	}

	/**
	 * Returns the given word with all variables translated to integer.
	 */
	public static Map<Term, List<Integer>> parseMoNatDiffToInteger(final NestedWord<MoNatDiffAlphabetSymbol> word,
			final Term... terms) {

		final Map<Term, List<Integer>> result = new HashMap<Term, List<Integer>>();

		// if (word.length() > 0) {
		// final Set<Term> terms = word.getSymbol(0).getMap().keySet();

		for (final Term term : terms)
			result.put(term, new ArrayList<Integer>());

		for (int i = 0; i < word.length(); i++) {
			final MoNatDiffAlphabetSymbol symbol = word.getSymbol(i);

			for (final Term term : terms) {
				if (symbol.getMap().get(term))
					result.get(term).add(i);
			}
		}
		// }

		return result;
	}
}