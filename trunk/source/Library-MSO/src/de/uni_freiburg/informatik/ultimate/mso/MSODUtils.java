/*
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE MSO Library package.
 *
 * The ULTIMATE MSO Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSO Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSO Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSO Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSO Library package library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Simplify handling of {@link Sort}s and {@link MSODAlphabetSymbol} used in MSOD-logic.
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
	 * Returns a set of integer constant that respects the UltimateNormalForm. See {@link UltimateNormalFormUtils}.
	 */
	public static Term constructSetOfIntValue(final Script script, final Set<BigInteger> numbers) {
		final Set<Term> terms = new HashSet<>();

		for (final BigInteger number : numbers) {
			terms.add(SmtUtils.constructIntValue(script, number));
		}

		return MSODUtils.getSetOfIntSort(script).getTheory().constant(terms, MSODUtils.getSetOfIntSort(script));
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
	 * Returns the alphabet for the given variable names. Alphabet symbols are mapped to its string representation.
	 */
	public static Map<String, MSODAlphabetSymbol> createAlphabet(final Term term) {
		final Map<String, MSODAlphabetSymbol> symbols = new HashMap<>();

		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(term, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(term, true);

		symbols.put("x0", x0);
		symbols.put("x1", x1);

		return symbols;
	}

	/**
	 * Returns the alphabet for the given variable names. Alphabet symbols are mapped to its string representation.
	 */
	public static Map<String, MSODAlphabetSymbol> createAlphabet(final Term term1, final Term term2) {
		final Map<String, MSODAlphabetSymbol> symbols = new HashMap<>();

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
	 * Returns the alphabet symbols where all but the excluded variables match the given value.
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

	/*
	 * Returns all Terms included in the given symbol which match the given sort.
	 */
	public static Set<Term> containsSort(final Set<MSODAlphabetSymbol> symbols, final String sort) {

		return containsSort(symbols, new HashSet<>(Arrays.asList(sort)));
	}

	/*
	 * Returns all Terms included in the given symbol which match one of the given sorts.
	 */
	public static Set<Term> containsSort(final Set<MSODAlphabetSymbol> symbols, final Set<String> sorts) {
		final Set<Term> result = new HashSet<>();

		for (final MSODAlphabetSymbol symbol : symbols) {
			result.addAll(symbol.containsSort(sorts));
		}

		return result;
	}

	/**
	 * Returns the successors which are directly reachable with the given symbols from the given state in the given
	 * automaton.
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
	 * Returns the predecessors which are directly reachable with the given symbols from the given state in the given
	 * automaton.
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
	public static Map<Term, Term> parseMSODNatToTerm(final Script script, final Word<MSODAlphabetSymbol> word) {

		if (word.length() <= 0) {
			return new HashMap<>();
		}

		return parseMSODNatToTerm(script, word, word.getSymbol(0).getTerms());
	}

	/**
	 * Returns a map which holds all terms and their values parsed from given word.
	 */
	public static Map<Term, Term> parseMSODNatToTerm(final Script script, final Word<MSODAlphabetSymbol> word,
			final Set<Term> terms) {

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

				final BigInteger value = values.get(term).iterator().next();
				result.put(term, SmtUtils.constructIntValue(script, value));
			}

			if (MSODUtils.isSetOfIntSort(term.getSort())) {
				result.put(term, MSODUtils.constructSetOfIntValue(script, values.get(term)));
			}
		}

		return result;
	}

	/**
	 * Returns a map which holds all terms and their values parsed from given word.
	 */
	public static Map<Term, Term> parseMSODIntToTerm(final Script script, final Word<MSODAlphabetSymbol> word) {

		if (word.length() <= 0) {
			return new HashMap<>();
		}

		return parseMSODIntToTerm(script, word, word.getSymbol(0).getTerms());
	}

	/**
	 * Returns a map which holds all terms and their values parsed from given word.
	 */
	public static Map<Term, Term> parseMSODIntToTerm(final Script script, final Word<MSODAlphabetSymbol> word,
			final Set<Term> terms) {

		final Map<Term, Term> result = new HashMap<>();
		final Map<Term, Set<BigInteger>> values = new HashMap<>();

		for (final Term term : terms) {
			values.put(term, new HashSet<BigInteger>());
		}

		for (int i = 0; i < word.length(); i++) {
			final MSODAlphabetSymbol symbol = word.getSymbol(i);

			for (final Term term : terms) {
				if (symbol.getMap().get(term)) {
					if (i % 2 == 0) {
						values.get(term).add(BigInteger.valueOf(-i / 2));
					} else {
						values.get(term).add(BigInteger.valueOf((i + 1) / 2));
					}
				}
			}
		}

		for (final Term term : values.keySet()) {
			if (SmtSortUtils.isIntSort(term.getSort())) {
				assert (values.get(term) != null && values.get(term).size() == 1);

				final BigInteger value = values.get(term).iterator().next();
				result.put(term, SmtUtils.constructIntValue(script, value));
			}

			if (MSODUtils.isSetOfIntSort(term.getSort())) {
				result.put(term, MSODUtils.constructSetOfIntValue(script, values.get(term)));
			}
		}

		return result;
	}
}