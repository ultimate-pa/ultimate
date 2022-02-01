/*
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE MSOD Library package.
 *
 * The ULTIMATE MSOD Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSOD Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSOD Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSOD Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSOD Library package library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
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

	private MSODUtils() {
		throw new UnsupportedOperationException("Instantiation of utility class.");
	}

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
	 * TODO: Maybe overload in {@link SmtUtils}.
	 */
	public static Term intConstant(final Script script, final int number) {
		return SmtUtils.constructIntValue(script, BigInteger.valueOf(number));
	}

	/**
	 * Returns the MSOD alphabet that contains the given variable names.
	 */
	public static Set<MSODAlphabetSymbol> createAlphabet(final List<Term> terms) {
		final Set<MSODAlphabetSymbol> symbols = new HashSet<>();

		for (int i = 0; i < (int) Math.pow(2, terms.size()); i++) {
			final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();

			for (int j = 0; j < terms.size(); j++) {
				final int value = (i / (int) Math.pow(2, j)) % 2;
				symbol.add(terms.get(j), value == 1);
			}
			symbols.add(symbol);
		}

		return symbols;
	}

	/**
	 * Returns the merged alphabet for given inputs.
	 */
	public static Set<MSODAlphabetSymbol> mergeAlphabets(final Set<MSODAlphabetSymbol> symbols1,
			final Set<MSODAlphabetSymbol> symbols2) {

		final Set<Term> terms = new HashSet<>();

		if (!symbols1.isEmpty()) {
			terms.addAll(symbols1.iterator().next().getMap().keySet());
		}

		if (!symbols2.isEmpty()) {
			terms.addAll(symbols2.iterator().next().getMap().keySet());
		}

		return createAlphabet(new ArrayList<>(terms));
	}

	/**
	 * Returns the alphabet symbols where all but the excluded variables match the given value.
	 */
	public static Set<MSODAlphabetSymbol> allMatchesAlphabet(final Set<MSODAlphabetSymbol> symbols, final Boolean value,
			final Term... excludedTerms) {

		final Set<MSODAlphabetSymbol> matches = new HashSet<>();
		symbols.stream().filter(e -> e.allMatches(value, excludedTerms)).forEach(e -> matches.add(e));

		return matches;
	}

	/**
	 * Returns the predecessor states from which the given state is directly reachable with the given symbol in the
	 * {@link INestedWordAutomaton}.
	 */
	public static Set<String> hierarchicalPredecessorsIncoming(
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final String state,
			final MSODAlphabetSymbol symbol) {

		final Set<String> result = new HashSet<>();
		for (final IncomingInternalTransition<MSODAlphabetSymbol, String> transition : automaton
				.internalPredecessors(state, symbol)) {

			result.add(transition.getPred());
		}

		return result;
	}

	/**
	 * Returns a string representation of the given automaton.
	 */
	public static String automatonToString(final AutomataLibraryServices services, final IAutomaton<?, ?> automaton) {
		return AutomatonDefinitionPrinter.toString(services, "", automaton);
	}
}