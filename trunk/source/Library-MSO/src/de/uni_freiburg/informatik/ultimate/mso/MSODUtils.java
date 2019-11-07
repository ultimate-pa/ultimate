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

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
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
	 * Returns sort SetOfInt.
	 */
	public static Sort getSetOfIntSort(final Script script) {
		return script.sort(SET_OF_INT_SORT);
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
		return SmtUtils.isConstant(term) && SmtSortUtils.isIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a SetOfInt constant.
	 */
	public static boolean isSetOfIntConstant(final Term term) {
		return SmtUtils.isConstant(term) && isSetOfIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a Int {@link TermVariable}.
	 */
	public static boolean isIntTermVariable(final Term term) {
		return term instanceof TermVariable && SmtSortUtils.isIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a SetOfInt {@link TermVariable}.
	 */
	public static boolean isSetOfIntTermVariable(final Term term) {
		return term instanceof TermVariable && isSetOfIntSort(term.getSort());
	}

	/**
	 * Returns true if term is a constant.
	 */
	public static boolean isConstant(final Term term) {
		return isIntConstant(term) || isSetOfIntConstant(term);
	}

	/**
	 * Returns true if term is a {@link TermVariable}.
	 */
	public static boolean isTermVariable(final Term term) {
		return isIntTermVariable(term) || isSetOfIntTermVariable(term);
	}

	/**
	 * Returns true if term is a constant or a {@link TermVariable}.
	 */
	public static boolean isConstantOrTermVariable(final Term term) {
		return isConstant(term) || isTermVariable(term);
	}

	/**
	 * Returns true if term is an Int constant or an Int {@link TermVariable}.
	 */
	public static boolean isIntConstantOrTermVariable(final Term term) {
		return isIntConstant(term) || isIntTermVariable(term);
	}

	/**
	 * Returns true if term is a SetOfInt constant or an SetOfInt {@link TermVariable}.
	 */
	public static boolean isSetOfIntConstantOrTermVariable(final Term term) {
		return isSetOfIntConstant(term) || isSetOfIntTermVariable(term);
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
}