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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class provides methods to construct automata that correspond to a given MSOD-Formula.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public abstract class MSODFormulaOperations {

	/**
	 * Returns a map term to numbers from the given {@link NestedWord}.
	 */
	public Map<Term, List<Integer>> wordToNumbers(final NestedWord<MSODAlphabetSymbol> word, final int offset) {
		final Map<Term, List<Integer>> result = new HashMap<>();

		for (int i = 0; i < word.length(); i++) {
			final int value = indexToInteger(i + offset);
			final MSODAlphabetSymbol symbol = word.getSymbol(i);

			for (final Entry<Term, Boolean> entry : symbol.getMap().entrySet()) {
				result.putIfAbsent(entry.getKey(), new ArrayList<>());

				if (!entry.getValue()) {
					continue;
				}

				if (value < 0) {
					result.get(entry.getKey()).add(0, value);
					continue;
				}

				result.get(entry.getKey()).add(value);
			}
		}

		return result;
	}

	/**
	 * TODO: Comment.
	 */
	public static Term stemResult(final Script script, final Term term, final List<Integer> numbers) {

		if (term.getSort().equals(SmtSortUtils.getIntSort(script))) {
			assert (numbers.size() == 1) : "Int variable must have exactly one value.";
			return MSODUtils.intConstant(script, numbers.get(0));
		}

		Term result = script.term("false");
		final Term x = term.getTheory().createTermVariable("x", SmtSortUtils.getIntSort(script));
		Integer start = null;

		for (int i = 0; i < numbers.size(); i++) {

			if (i + 1 < numbers.size() && numbers.get(i) == numbers.get(i + 1) - 1) {
				if (start == null) {
					start = numbers.get(i);
				}
				continue;
			}

			if (start == null) {
				final Term eq = SmtUtils.binaryEquality(script, x, MSODUtils.intConstant(script, numbers.get(i)));
				result = SmtUtils.or(script, result, eq);
				continue;
			}

			final Term geq = SmtUtils.geq(script, x, MSODUtils.intConstant(script, start));
			final Term leq = SmtUtils.leq(script, x, MSODUtils.intConstant(script, numbers.get(i)));
			result = SmtUtils.or(script, result, SmtUtils.and(script, geq, leq));
			start = null;
		}

		return result;
	}

	/**
	 * TODO: Comment.
	 */
	public static Term loopResultPartial(final Script script, final Term term, final List<Integer> numbers,
			final Integer bound, final int loopLength) {

		Term result = script.term("false");
		final Term x = term.getTheory().createTermVariable("x", SmtSortUtils.getIntSort(script));
		Integer start = null;

		for (int i = 0; i < numbers.size(); i++) {

			if (i + 1 < numbers.size() && numbers.get(i) == numbers.get(i + 1) - 1) {
				if (start == null) {
					start = numbers.get(i);
				}
				continue;
			}

			final Term lhs = SmtUtils.mod(script, x, MSODUtils.intConstant(script, loopLength));

			if (start == null) {
				final Term rhs = MSODUtils.intConstant(script, numbers.get(i) % loopLength);
				final Term eq = SmtUtils.binaryEquality(script, lhs, rhs);
				result = SmtUtils.or(script, result, eq);
				continue;
			}

			final Term geq = SmtUtils.geq(script, lhs, MSODUtils.intConstant(script, start % loopLength));
			final Term leq = SmtUtils.leq(script, lhs, MSODUtils.intConstant(script, numbers.get(i) % loopLength));
			result = SmtUtils.or(script, result, SmtUtils.and(script, geq, leq));
			start = null;
		}

		final Term stemNumber = MSODUtils.intConstant(script, bound);
		final Term stemBound = (bound < 0) ? SmtUtils.leq(script, x, stemNumber) : SmtUtils.geq(script, x, stemNumber);

		return SmtUtils.and(script, result, stemBound);
	}

	/**
	 * TODO: Comment.
	 */
	public static Term loopResult(final Script script, final Term term, final List<Integer> numbers,
			final Pair<Integer, Integer> bounds, final int loopLength) {

		final List<Integer> neg = new ArrayList<>();
		final List<Integer> pos = new ArrayList<>();

		for (final Integer number : numbers) {
			if (number < 0) {
				neg.add(number);
				continue;
			}
			pos.add(number);
		}

		final Term t1 = loopResultPartial(script, term, neg, bounds.getFirst(), loopLength);
		final Term t2 = loopResultPartial(script, term, pos, bounds.getSecond(), loopLength);

		return SmtUtils.or(script, t1, t2);
	}

	/**
	 * Returns an empty {@link NestedWordAutomaton}.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String>
			emptyAutomaton(final AutomataLibraryServices services) {

		return new NestedWordAutomaton<>(services, new VpAlphabet<>(new HashSet<>()), new MSODStringFactory());
	}

	/**
	 * Returns an {@link NestedWordAutomaton} that represents "true".
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String>
			trueAutomaton(final AutomataLibraryServices services) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, true, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Returns an {@link NestedWordAutomaton} that represents "false".
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String>
			falseAutomaton(final AutomataLibraryServices services) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, false, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a strict inequality of the form "x < c".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c);

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a strict inequality of the form "x-y < c".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictIneqAutomaton(final AutomataLibraryServices services, final Term x, final Term y, final Rational c)
					throws AutomataLibraryException;

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a strict inequality of the form "-x < c".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c);

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a strict subset relation of the form "X ⊊ Y".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictSubsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y);

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a subset relation of the form "X ⊆ Y".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			subsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y);

	/**
	 * Returns an {@link INestedWordAutomaton} that represents an element relation of the form "x+c ∈ Y".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			elementAutomaton(final AutomataLibraryServices services, final Term x, final Rational c, final Term y)
					throws AutomataLibraryException;

	/**
	 * Returns an {@link INestedWordAutomaton} that represents an element relation of the form "c ∈ X".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			constElementAutomaton(final AutomataLibraryServices services, final Rational c, final Term x);

	/**
	 * Returns integer value that corresponds to the given index.
	 */
	public abstract int indexToInteger(final int index);

	/**
	 * Returns the exclusive stem bounds.
	 */
	public abstract Pair<Integer, Integer> stemBounds(final int length);
}