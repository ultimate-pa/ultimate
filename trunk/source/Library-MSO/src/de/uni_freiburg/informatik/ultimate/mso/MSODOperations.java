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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * TODO: Comment Class.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public final class MSODOperations {

	private final MSODFormulaOperations mFormulaOperations;
	private final MSODAutomataOperations mAutomataOperations;

	public MSODOperations(final MSODFormulaOperations formulaOperations,
			final MSODAutomataOperations automataOperations) {

		mFormulaOperations = formulaOperations;
		mAutomataOperations = automataOperations;
	}

	public NestedWordAutomaton<MSODAlphabetSymbol, String> trueAutomaton(final AutomataLibraryServices services) {

		return mFormulaOperations.trueAutomaton(services);
	}

	public NestedWordAutomaton<MSODAlphabetSymbol, String> falseAutomaton(final AutomataLibraryServices services) {

		return mFormulaOperations.falseAutomaton(services);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational c) {

		return mFormulaOperations.strictIneqAutomaton(services, x, c);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y, final Rational c) throws AutomataLibraryException {

		return mFormulaOperations.strictIneqAutomaton(services, x, y, c);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c) {

		return mFormulaOperations.strictNegIneqAutomaton(services, x, c);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictSubsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y) {

		return mFormulaOperations.strictSubsetAutomaton(services, x, y);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> subsetAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y) {

		return mFormulaOperations.subsetAutomaton(services, x, y);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational c, final Term y) throws AutomataLibraryException {

		return mFormulaOperations.elementAutomaton(services, x, c, y);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String>
			constElementAutomaton(final AutomataLibraryServices services, final Rational c, final Term x) {

		return mFormulaOperations.constElementAutomaton(services, c, x);
	}

	public NestedWordAutomaton<MSODAlphabetSymbol, String> reconstruct(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<MSODAlphabetSymbol> alphabet,
			final boolean isExtended) {

		return mAutomataOperations.reconstruct(services, automaton, alphabet, isExtended);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> complement(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		return mAutomataOperations.complement(services, automaton);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> union(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		return mAutomataOperations.union(services, automaton1, automaton2);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> intersect(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		return mAutomataOperations.intersect(services, automaton1, automaton2);
	}

	public INestedWordAutomaton<MSODAlphabetSymbol, String> makeStatesFinal(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<String> states)
			throws AutomataLibraryException {

		return mAutomataOperations.makeStatesFinal(services, automaton, states);
	}

	/**
	 * Returns a {@link NestedWord} accepted by the given automaton, or null if language of automaton is empty.
	 *
	 * @throws AutomataLibraryException
	 *             if {@link IsEmpty} fails
	 */
	public NestedWord<MSODAlphabetSymbol> getWordWeak(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		NestedWord<MSODAlphabetSymbol> result = null;

		final IsEmpty<MSODAlphabetSymbol, String> isEmpty = new IsEmpty<>(services, automaton);

		if (!isEmpty.getResult()) {
			final NestedRun<MSODAlphabetSymbol, String> run = isEmpty.getNestedRun();
			result = run.getWord();
		}

		return result;
	}

	/**
	 * Returns a {@link NestedLassoWord} accepted by the given automaton, or null if language of automaton is empty.
	 *
	 * @throws AutomataLibraryException
	 *             if {@link BuchiIsEmpty} fails
	 */
	public NestedLassoWord<MSODAlphabetSymbol> getWordBuchi(final Script script, final AutomataLibraryServices services,
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
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given automata or null if no such model
	 * exists. Each combination of Finite Automata resp. Büchi Automata with Natural numbers resp. Integer numbers
	 * requires its own getResult method.
	 *
	 * @throws AutomataLibraryException
	 */
	public Map<Term, Term> getResult(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
		if (mAutomataOperations instanceof MSODAutomataOperationsWeak) {
			return getResultWeak(script, services, automaton);
		}
		if (mAutomataOperations instanceof MSODAutomataOperationsBuchi) {
			return getResultBuchi(script, services, automaton);
		}
		return null;
	}

	// Returns the range of consecutive numbers in the given array as a set of arrays. Each array in the result contains
	// the start resp. end number of one series of consecutive numbers.
	public Set<Pair<Integer, Integer>> getRangeOfConsecutiveNumbers(final Set<Integer> num) {

		final List<Integer> numbers = new ArrayList<>();
		numbers.addAll(num);
		numbers.sort(null);

		final Set<Pair<Integer, Integer>> result = new HashSet<>();
		Integer start = null;
		Integer end = null;

		for (int i = 0; i < numbers.size(); i++) {
			if (i == 0) {
				start = numbers.get(i);
				end = numbers.get(i);
			} else {
				if (numbers.get(i) - end == 1) {
					end = numbers.get(i);
				} else {
					result.add(new Pair<>(start, end));
					start = numbers.get(i);
					end = numbers.get(i);
				}
			}
			if (i == numbers.size() - 1) {
				result.add(new Pair<>(start, end));
			}
		}
		return result;
	}

	// Constructs a disjunction of terms corresponding to the given set of consecutive numbers derived from the stem.
	public Term createStemTerm(final Script script, final Term term, final Set<Pair<Integer, Integer>> numbers) {
		final Iterator<Pair<Integer, Integer>> it = numbers.iterator();
		Term result = null;

		// TODO: make sure start == end for integer
		if (SmtSortUtils.isIntSort(term.getSort()) && numbers.size() != 1) {
			throw new InternalError("The Integer representation is corrupted!");
		}

		while (it.hasNext()) {
			final Pair<Integer, Integer> pair = it.next();
			final Integer start = pair.getFirst();
			final Integer end = pair.getSecond();
			final Term setTerm = script.variable(term.toString(), SmtSortUtils.getIntSort(script));
			Term t;

			// Direcetly return first value if term represents an Integer variable.
			if (SmtSortUtils.isIntSort(term.getSort()) && start == end) {
				return SmtUtils.constructIntValue(script, BigInteger.valueOf(start));
			}

			// If pair represents a single number, construct term of the form "variable = value"
			if (start == end) {
				t = SmtUtils.binaryEquality(script, setTerm,
						SmtUtils.constructIntValue(script, BigInteger.valueOf(start)));
			} else {
				// If pair represents a series of numbers, construct a term of the form
				// "(variable >=startValue) && (variable <= endValue)"
				final Term t1 =
						SmtUtils.geq(script, setTerm, SmtUtils.constructIntValue(script, BigInteger.valueOf(start)));
				final Term t2 =
						SmtUtils.leq(script, setTerm, SmtUtils.constructIntValue(script, BigInteger.valueOf(end)));
				t = SmtUtils.and(script, t1, t2);
			}
			result = (result != null) ? SmtUtils.or(script, result, t) : t;
		}
		return result;
	}

	// Returns a pair of NestedWords. First value contains only the positive part, second value only the negative part
	// of the given NestedWord.
	public Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>> splitWordWeak(final Script script,
			final NestedWord<MSODAlphabetSymbol> word, final MSODFormulaOperations formulaOperation) {
		NestedWord<MSODAlphabetSymbol> wordPos = new NestedWord<>();
		NestedWord<MSODAlphabetSymbol> wordNeg = new NestedWord<>();

		if (formulaOperation instanceof MSODFormulaOperationsNat) {
			wordPos = word;
		}
		if (formulaOperation instanceof MSODFormulaOperationsInt) {
			final List<MSODAlphabetSymbol> symbolsPos = new ArrayList<>();
			final List<MSODAlphabetSymbol> symbolsNeg = new ArrayList<>();
			;
			for (int i = 0; i < word.length(); i++) {
				if (i % 2 == 0) {
					symbolsNeg.add(word.getSymbol(i));
				} else {
					symbolsPos.add(word.getSymbol(i));
				}
			}
			wordPos = NestedWord.nestedWord(new Word<>((MSODAlphabetSymbol[]) symbolsPos.toArray()));
			wordNeg = NestedWord.nestedWord(new Word<>((MSODAlphabetSymbol[]) symbolsNeg.toArray()));
		}
		return new Pair<>(wordPos, wordNeg);
	}

	// Returns a pair of NestedLassoWords. First value contains only the positive part, second value only the negative
	// part of the given NestedLassoWord.
	public Pair<NestedLassoWord<MSODAlphabetSymbol>, NestedLassoWord<MSODAlphabetSymbol>> splitWordBuchi(
			final Script script, NestedLassoWord<MSODAlphabetSymbol> word,
			final MSODFormulaOperations formulaOperation) {
		NestedLassoWord<MSODAlphabetSymbol> lassoWordPos = new NestedLassoWord<>(null, null);
		NestedLassoWord<MSODAlphabetSymbol> lassoWordNeg = new NestedLassoWord<>(null, null);

		if (formulaOperation instanceof MSODFormulaOperationsNat) {
			lassoWordPos = word;
		}
		if (formulaOperation instanceof MSODFormulaOperationsInt) {
			final List<MSODAlphabetSymbol> symbolsPosStem = new ArrayList<>();
			final List<MSODAlphabetSymbol> symbolsPosLoop = new ArrayList<>();
			final List<MSODAlphabetSymbol> symbolsNegStem = new ArrayList<>();
			final List<MSODAlphabetSymbol> symbolsNegLoop = new ArrayList<>();

			final Boolean fstLoopNumIsNeg = (word.getStem().length() % 2 == 0) ? true : false;

			// Deal with loop of odd length.
			if (word.getLoop().length() % 2 == 1) {
				word = new NestedLassoWord<>(word.getStem(), word.getLoop().concatenate(word.getLoop()));
			}

			// Split stem into positive resp. negative part.
			for (int i = 0; i < word.getStem().length(); i++) {
				if (i % 2 == 0) {
					symbolsNegStem.add(word.getStem().getSymbol(i / 2));
				} else {
					symbolsPosStem.add(word.getStem().getSymbol((i - 1) / 2));
				}
			}

			// Split loop into positive resp. negative part.
			int j = 0;
			for (int i = 0; i < word.getLoop().length(); i++) {
				if (!fstLoopNumIsNeg) {
					j = 1;
				}
				if (i % 2 == j) {
					symbolsNegLoop.add(word.getLoop().getSymbol(i / 2));
				} else {
					symbolsPosLoop.add(word.getLoop().getSymbol((i - 1) / 2));
				}
			}

			// Create new LassoWords
			final NestedWord<MSODAlphabetSymbol> stemPos =
					NestedWord.nestedWord(new Word<>((MSODAlphabetSymbol[]) symbolsPosStem.toArray()));
			final NestedWord<MSODAlphabetSymbol> loopPos =
					NestedWord.nestedWord(new Word<>((MSODAlphabetSymbol[]) symbolsPosLoop.toArray()));
			final NestedWord<MSODAlphabetSymbol> stemNeg =
					NestedWord.nestedWord(new Word<>((MSODAlphabetSymbol[]) symbolsNegStem.toArray()));
			final NestedWord<MSODAlphabetSymbol> loopNeg =
					NestedWord.nestedWord(new Word<>((MSODAlphabetSymbol[]) symbolsNegLoop.toArray()));

			lassoWordPos = new NestedLassoWord<>(stemPos, loopPos);
			lassoWordNeg = new NestedLassoWord<>(stemNeg, loopNeg);
		}
		return new Pair<>(lassoWordPos, lassoWordNeg);
	}

	/**
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given automata or null if no such model
	 * exists.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	public Map<Term, Term> getResultWeak(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException, UnsupportedOperationException {
		final Map<Term, Term> result = new HashMap<>();
		final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();

		// Get the word of the accepted run and split it into positive and negative parts.
		final NestedWord<MSODAlphabetSymbol> word = getWordWeak(script, services, automaton);
		final Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>> splittedWord =
				splitWordWeak(script, word, mFormulaOperations);
		final NestedWord<MSODAlphabetSymbol> wordPos = splittedWord.getFirst();
		final NestedWord<MSODAlphabetSymbol> wordNeg = splittedWord.getSecond();

		Map<Term, Set<Integer>> setPos = new HashMap<>();
		Map<Term, Set<Integer>> setNeg = new HashMap<>();

		// Get the numbers encoded in the word.
		if (wordPos != null) {
			setPos = getNumbersFromWord(wordPos, terms, true);
		}
		if (wordNeg != null) {
			setNeg = getNumbersFromWord(wordNeg, terms, false);
		}

		// Find the ranges of consecutive numbers for each term, and construct stem condition.
		for (final Term term : terms) {
			final Set<Integer> numbers = new HashSet<>();
			if (!setPos.isEmpty()) {
				numbers.addAll(setPos.get(term));
			}
			if (!setNeg.isEmpty()) {
				numbers.addAll(setNeg.get(term));
			}
			final Set<Pair<Integer, Integer>> consecutiveNumbers = getRangeOfConsecutiveNumbers(numbers);

			result.put(term, createStemTerm(script, term, consecutiveNumbers));
		}
		return result;
	}

	public Map<Term, Term> getResultBuchi(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
		final Map<Term, Term> result = new HashMap<>();
		final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();

		// Get word of accepting run and split it into positive and negative parts.
		final NestedLassoWord<MSODAlphabetSymbol> word = getWordBuchi(script, services, automaton);
		final Pair<NestedLassoWord<MSODAlphabetSymbol>, NestedLassoWord<MSODAlphabetSymbol>> pair =
				splitWordBuchi(script, word, mFormulaOperations);
		final NestedLassoWord<MSODAlphabetSymbol> wordPos = pair.getFirst();
		final NestedLassoWord<MSODAlphabetSymbol> wordNeg = pair.getSecond();

		Map<Term, Set<Integer>> stemNumbersPos = new HashMap<>();
		Map<Term, Set<Integer>> loopNumbersPos = new HashMap<>();
		Map<Term, Set<Integer>> stemNumbersNeg = new HashMap<>();
		Map<Term, Set<Integer>> loopNumbersNeg = new HashMap<>();
		int maxStem = -1;
		int minStem = 1;

		// Get the numbers encoded in the stem rsp. loop and the maximal resp. minimal number that could be represented
		// by the stem.
		if (wordPos != null) {
			stemNumbersPos = getNumbersFromWord(wordPos.getStem(), terms, true);
			maxStem = wordPos.getStem().length();
			loopNumbersPos = getNumbersFromWord(wordPos.getLoop(), terms, true);
		}
		if (wordNeg != null) {
			stemNumbersNeg = getNumbersFromWord(wordNeg.getStem(), terms, false);
			minStem = -(wordNeg.getStem().length() - 1);
			loopNumbersNeg = getNumbersFromWord(wordNeg.getLoop(), terms, false);
		}

		if (!loopNumbersNeg.isEmpty()) {

		}

		// Find the ranges of consecutive numbers for each term, and construct stem condition.
		final Map<Term, Term> stemTerms = new HashMap<>();
		for (final Term term : terms) {
			final Set<Integer> numbers = new HashSet<>();

			if (!stemNumbersPos.isEmpty()) {
				numbers.addAll(stemNumbersPos.get(term));
			}
			if (!stemNumbersNeg.isEmpty()) {
				numbers.addAll(stemNumbersNeg.get(term));
			}

			final Set<Pair<Integer, Integer>> consecutiveNumbers = getRangeOfConsecutiveNumbers(numbers);
			stemTerms.put(term, createStemTerm(script, term, consecutiveNumbers));
		}
		return result;
	}

	public Map<Term, Set<Integer>> getNumbersFromWord(final NestedWord<MSODAlphabetSymbol> word, final Set<Term> terms,
			final Boolean isPositive) {

		final Map<Term, Set<Integer>> result = new HashMap<>();

		for (final Term term : terms) {
			result.put(term, new HashSet<>());
		}

		// Compute the number that is represented by the given index.
		for (int i = 0; i < word.length(); i++) {
			final MSODAlphabetSymbol symbol = word.getSymbol(i);
			for (final Entry<Term, Boolean> entry : symbol.getMap().entrySet()) {
				if (entry.getValue()) {
					if (isPositive) {
						result.get(entry.getKey()).add(i + 1);
					} else {
						result.get(entry.getKey()).add(-i);
					}
				}
			}
		}

		return result;
	}

}