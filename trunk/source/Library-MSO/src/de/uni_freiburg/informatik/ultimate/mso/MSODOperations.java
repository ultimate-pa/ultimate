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

import java.lang.reflect.Array;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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
 * This class provides methods to construct and manipulate automata used to describe MSOD-Formulas.
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

	public NestedWordAutomaton<MSODAlphabetSymbol, String> copyAutomaton(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) {
		return mAutomataOperations.copyAutomaton(services, automaton);
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
	 * Returns a pair of NestedWords. First value contains only the positive part, second value only the negative part
	 * of the given NestedWord.
	 */
	public Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>> splitWordWeak(final Script script,
			final NestedWord<MSODAlphabetSymbol> word) {
		NestedWord<MSODAlphabetSymbol> wordPos = new NestedWord<>();
		NestedWord<MSODAlphabetSymbol> wordNeg = new NestedWord<>();

		final List<MSODAlphabetSymbol> symbolsPos = new ArrayList<>();
		final List<MSODAlphabetSymbol> symbolsNeg = new ArrayList<>();

		for (int i = 0; i < word.length(); i++) {
			if (i % 2 == 0) {
				symbolsPos.add(word.getSymbol(i));
			} else {
				symbolsNeg.add(word.getSymbol(i));
			}
		}

		wordPos = NestedWord
				.nestedWord(new Word<>(symbolsPos.toArray(new MSODAlphabetSymbol[(int) (0.5 * word.length() + 0.5)])));
		wordNeg = NestedWord
				.nestedWord(new Word<>(symbolsNeg.toArray(new MSODAlphabetSymbol[(int) (0.5 * word.length())])));

		return new Pair<>(wordPos, wordNeg);
	}

	/**
	 * Returns a pair of NestedLassoWords. First value contains only the positive part, second value only the negative
	 * part of the given NestedLassoWord.
	 */
	public Pair<NestedLassoWord<MSODAlphabetSymbol>, NestedLassoWord<MSODAlphabetSymbol>>
			splitWordBuchi(final Script script, NestedLassoWord<MSODAlphabetSymbol> word) {
		NestedLassoWord<MSODAlphabetSymbol> lassoWordPos = new NestedLassoWord<>(null, null);
		NestedLassoWord<MSODAlphabetSymbol> lassoWordNeg = new NestedLassoWord<>(null, null);

		Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>> stemPair;

		final List<MSODAlphabetSymbol> symbolsPosLoop = new ArrayList<>();
		final List<MSODAlphabetSymbol> symbolsNegLoop = new ArrayList<>();

		// The loop must be unrolled once in case of odd loop length.
		if (word.getLoop().length() % 2 == 1) {
			word = new NestedLassoWord<>(word.getStem(), word.getLoop().concatenate(word.getLoop()));
		}

		// Split stem into positive resp. negative part.
		stemPair = splitWordWeak(script, word.getStem());

		// Split loop into positive resp. negative part. The order of positive and negative numbers in the loop is
		// reversed if the stem length is odd.
		for (int i = 0; i < word.getLoop().length(); i++) {
			if (i % 2 == word.getStem().length() % 2) {
				symbolsPosLoop.add(word.getLoop().getSymbol(i));
			} else {
				symbolsNegLoop.add(word.getLoop().getSymbol(i));
			}
		}

		final MSODAlphabetSymbol[] symbolP =
				(MSODAlphabetSymbol[]) Array.newInstance(MSODAlphabetSymbol.class, symbolsPosLoop.size());
		final MSODAlphabetSymbol[] symbolN =
				(MSODAlphabetSymbol[]) Array.newInstance(MSODAlphabetSymbol.class, symbolsPosLoop.size());
		for (int i = 0; i < symbolsPosLoop.size(); i++) {
			Array.set(symbolP, i, symbolsPosLoop.get(i));
		}

		for (int i = 0; i < symbolsNegLoop.size(); i++) {
			Array.set(symbolN, i, symbolsNegLoop.get(i));
		}

		// Create positive resp. negative LassoWords.

		final NestedWord<MSODAlphabetSymbol> loopPos = NestedWord.nestedWord(new Word<>(symbolP));
		final NestedWord<MSODAlphabetSymbol> loopNeg = NestedWord.nestedWord(new Word<>(symbolN));

		lassoWordPos = new NestedLassoWord<>(stemPair.getFirst(), loopPos);
		lassoWordNeg = new NestedLassoWord<>(stemPair.getSecond(), loopNeg);

		return new Pair<>(lassoWordPos, lassoWordNeg);
	}

	/**
	 * Returns a Map containing terms and the set of numbers encoded in the stem.
	 */
	public Map<Term, Set<BigInteger>> extractStemNumbers(final Script script,
			final Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>> pair, final Set<Term> terms) {

		final Map<Term, Set<BigInteger>> result = new HashMap<>();
		for (final Term term : terms) {
			result.put(term, null);
		}

		for (final Term term : terms) {
			final Set<BigInteger> numbers = new HashSet<>();
			// Extract numbers from positive stem.
			if (pair.getFirst() != null) {

				for (int i = 0; i < pair.getFirst().length(); i++) {
					if (pair.getFirst().getSymbol(i).getMap().get(term)) {
						numbers.add(BigInteger.valueOf(i));
					}
				}
			}
			// Extract numbers from negative stem.
			if (pair.getSecond() != null) {
				for (int i = 0; i < pair.getSecond().length(); i++) {
					if (pair.getSecond().getSymbol(i).getMap().get(term)) {
						numbers.add(BigInteger.valueOf(-(i + 1)));
					}
				}
			}
			result.put(term, numbers);
		}
		return result;
	}

	/**
	 * Returns a Map containing terms and the disjunction corresponding to the numbers encoded in the given stem.
	 */
	public Map<Term, Term> constructStemTerm(final Script script, final Map<Term, Set<BigInteger>> stemNumbers) {
		final Map<Term, Term> result = new HashMap<>();

		for (final Entry<Term, Set<BigInteger>> entry : stemNumbers.entrySet()) {
			final List<BigInteger> list = new ArrayList<>(entry.getValue());
			Collections.sort(list);
			final Set<Term> disjuncts = new HashSet<>();
			BigInteger value = null;
			Term resultTerm = null;

			// Create new Term variable, with same name as original term variable but sort IntSort.
			final Term newTerm = entry.getKey().getTheory().createTermVariable(entry.getKey().toString(),
					SmtSortUtils.getIntSort(script));

			for (int i = 0; i < list.size(); i++) {
				// Start a new interval
				if (value == null) {
					value = list.get(i);
				}

				// Create and store term, if interval cannot be not prolonged.
				if (value != null & (i + 1 == list.size() || list.get(i + 1) != value.add(BigInteger.ONE))) {
					// Number is not part of an interval
					if (value == list.get(i)) {
						// Create single value term if sort of term is IntSort
						if (SmtSortUtils.isIntSort(entry.getKey().getSort())) {
							resultTerm = SmtUtils.constructIntValue(script, value);
						}
						// Create binary equality if sort is SetOfIntSOrt.
						else {
							resultTerm =
									SmtUtils.binaryEquality(script, newTerm, SmtUtils.constructIntValue(script, value));
						}
						// Create term describing an interval of numbers encoded in the stem.
					} else {
						final Term t1 = SmtUtils.constructIntValue(script, value);
						final Term t2 = SmtUtils.constructIntValue(script, list.get(i));
						final Term geq = SmtUtils.geq(script, newTerm, t1);
						final Term leq = SmtUtils.leq(script, newTerm, t2);

						resultTerm = SmtUtils.and(script, geq, leq);
					}

					disjuncts.add(resultTerm);
					value = null;
				}
			}

			// Build disjunction of all terms.
			if (!disjuncts.isEmpty()) {
				result.put(entry.getKey(), SmtUtils.or(script, disjuncts));
			} else {
				result.put(entry.getKey(), entry.getKey().getTheory().mFalse);
			}
		}
		return result;
	}

	/**
	 * Returns a Map containing terms and the disjunction corresponding to the numbers encoded in the given loop.
	 */
	public Map<Term, Term> constructLoopTerm(final Script script, final NestedWord<MSODAlphabetSymbol> loop,
			final Set<Term> terms, final int stemNumber) {
		final Map<Term, Term> result = new HashMap<>();
		final BigInteger loopLength = BigInteger.valueOf(loop.length());

		for (final Term term : terms) {
			// No IntSort variable should have indices enabled in its loop.
			if (SmtSortUtils.isIntSort(term.getSort())) {
				throw new InternalError("Integer representation is corrupted.");
			}

			final Set<Term> disjuncts = new HashSet<>();

			// Create new Term variable, with same name as original term variable but sort IntSort.
			final Term newTerm = term.getTheory().createTermVariable(term.toString(), SmtSortUtils.getIntSort(script));

			for (int i = 0; i < loop.length(); i++) {
				if (loop.getSymbol(i).getMap().get(term)) {
					final BigInteger value;

					if (stemNumber >= 0) {
						value = BigInteger.valueOf(i + 1 + stemNumber);
					} else {
						value = BigInteger.valueOf(-i - 1 + stemNumber);
					}

					// Construct 2 modulo-Terms: "Term-variable % loopLength" resp. "(i+1+|stemNumber|) % loopLength"
					final Term mod1 = SmtUtils.mod(script, newTerm, SmtUtils.constructIntValue(script, loopLength));
					final Term mod2 = SmtUtils.mod(script, SmtUtils.constructIntValue(script, value),
							SmtUtils.constructIntValue(script, loopLength));

					// Create and store binary equality of modulo Terms.
					disjuncts.add(SmtUtils.binaryEquality(script, mod1, mod2));
				}
			}

			// Build disjunction of all terms.
			if (!disjuncts.isEmpty()) {
				// Build disjunction of all terms.
				final Term disjunction = SmtUtils.or(script, disjuncts);

				// Add conjunct to exclude values already taken care of in the stem.
				Term conjunct = null;
				if (stemNumber >= 0) {
					conjunct = SmtUtils.greater(script, newTerm,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(stemNumber)));
				} else {
					conjunct = SmtUtils.less(script, newTerm,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(stemNumber)));
				}
				result.put(term, SmtUtils.and(script, conjunct, disjunction));
			} else {
				result.put(term, term.getTheory().mFalse);
			}
		}
		return result;
	}

	/**
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given automata or null if no such model
	 * exists. Finite Automata resp. Büchi Automata require their own getResult method.
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

	/**
	 * Returns a satisfying SMTLIB model for the Weak-MSOD-formula of type Nat represented by the given automata or null
	 * if no such model exists.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	public Map<Term, Term> getResultWeak(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException, UnsupportedOperationException {
		Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>> pair;

		// Get the word of the accepted run and the contained terms.
		final NestedWord<MSODAlphabetSymbol> word = getWordWeak(script, services, automaton);

		// No accepted run.
		if (word == null) {
			return null;
		}

		// Variable must represent the empty set. Deal with empty word.
		if (word.length() == 0) {
			// TODO: Construct lambda expression for empty word.
			final Map<Term, Term> result = new HashMap<>();
			result.put(SmtUtils.buildNewConstant(script, "emptyWord", SmtSortUtils.BOOL_SORT), null);
			return result;
		}

		final Set<Term> terms = word.getSymbol(0).getTerms();

		// Split word into positive and negative part if the input formula is defined for integer numbers.
		if (mFormulaOperations instanceof MSODFormulaOperationsInt) {
			pair = splitWordWeak(script, word);
		}
		// Input Formula defined only for natural numbers, no negative word exists.
		else {
			pair = new Pair<>(word, new NestedWord());
		}

		// Extract the numbers encoded in the stems.
		final Map<Term, Set<BigInteger>> numbers = extractStemNumbers(script, pair, terms);

		// Construct resulting stem terms from Set of numbers
		return constructStemTerm(script, numbers);
	}

	/**
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given Buchi automata or null if no such
	 * model exists.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	public Map<Term, Term> getResultBuchi(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException, UnsupportedOperationException {
		final Map<Term, Term> result = new HashMap<>();
		Pair<NestedLassoWord<MSODAlphabetSymbol>, NestedLassoWord<MSODAlphabetSymbol>> pair;

		// Get the word of the accepted run.
		final NestedLassoWord<MSODAlphabetSymbol> word = getWordBuchi(script, services, automaton);

		// No accepted run.
		if (word == null) {
			return null;
		}

		// Deal with empty word.
		if (word.getStem().length() + word.getLoop().length() == 0) {
			result.put(SmtUtils.buildNewConstant(script, "emptyWord", SmtSortUtils.BOOL_SORT), null);
			return result;
		}
		// Get the terms from of the accepted word.
		final Set<Term> terms = word.getStem().getSymbol(0).getTerms();

		final Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>> stemPair;
		// Split word into positive and negative part if the input formula is defined for integer numbers.
		if (mFormulaOperations instanceof MSODFormulaOperationsInt) {
			pair = splitWordBuchi(script, word);

		}
		// Input Formula defined only for natural numbers, no negative word exists.
		else {
			pair = new Pair<>(word, new NestedLassoWord(new NestedWord(), new NestedWord()));
		}

		stemPair = new Pair<>(pair.getFirst().getStem(), pair.getSecond().getStem());

		// Extract the numbers encoded in the stems.
		final Map<Term, Set<BigInteger>> numbers = extractStemNumbers(script, stemPair, terms);

		// Construct resulting stem terms from set of numbers.
		final Map<Term, Term> stemTerms = constructStemTerm(script, numbers);

		// Deal with loops
		Map<Term, Term> loopTermsPos = new HashMap<>();
		Map<Term, Term> loopTermsNeg = new HashMap<>();

		// Construct condition from positive loop part.
		if (pair.getFirst() != null) {
			final int maxStemNumber =
					pair.getFirst().getStem().length() > 0 ? pair.getFirst().getStem().length() - 1 : 0;
			loopTermsPos = constructLoopTerm(script, pair.getFirst().getLoop(), terms, maxStemNumber);
		}
		// Construct condition from negative loop part.
		if (pair.getSecond() != null) {
			final int minStemNumber =
					pair.getSecond().getStem().length() > 0 ? -pair.getSecond().getStem().length() : 0;
			loopTermsNeg = constructLoopTerm(script, pair.getSecond().getLoop(), terms, minStemNumber);
		}

		// Construct final result from stemTerms and loopTerms.
		for (final Term term : terms) {
			final Set<Term> set = new HashSet<>();

			if (stemTerms.get(term) != null) {
				set.add(stemTerms.get(term));
			}
			if (loopTermsPos.get(term) != null) {
				set.add(loopTermsPos.get(term));
			}
			if (loopTermsNeg.get(term) != null) {
				set.add(loopTermsNeg.get(term));
			}
			if (!set.isEmpty()) {
				result.put(term, SmtUtils.or(script, set));
			}
			// The term variable must represent the empty set.
			// TODO: Construct lambda expression for empty set.
			else {
				result.put(term, term.getTheory().mFalse);
			}
		}
		return result;
	}
}