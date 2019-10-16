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
import java.util.List;
import java.util.Map;
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
		if (mAutomataOperations instanceof MSODAutomataOperationsWeak
				& mFormulaOperations instanceof MSODFormulaOperationsNat) {
			return getResultNatWeak(script, services, automaton);
		}
		if (mAutomataOperations instanceof MSODAutomataOperationsWeak
				& mFormulaOperations instanceof MSODFormulaOperationsInt) {
			return getResultIntWeak(script, services, automaton);
		}
		if (mAutomataOperations instanceof MSODAutomataOperationsBuchi
				& mFormulaOperations instanceof MSODFormulaOperationsNat) {
			return getResultNatBuchi(script, services, automaton);
		}
		if (mAutomataOperations instanceof MSODAutomataOperationsBuchi
				&& mFormulaOperations instanceof MSODFormulaOperationsInt) {
			return getResultIntBuchi(script, services, automaton);
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
	public Map<Term, Term> testGetResultWeak(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException, UnsupportedOperationException {
		Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>> pair;

		// Get the word of the accepted run.
		final NestedWord<MSODAlphabetSymbol> word = getWordWeak(script, services, automaton);

		// Split word into positive and negative part if the input formula is defined for integer numbers.
		if (mAutomataOperations instanceof MSODAutomataOperationsWeak
				& mFormulaOperations instanceof MSODFormulaOperationsInt) {
			pair = splitWordWeak(script, word);
		}
		// Input Formula defined only for natural numbers, no negative word exists.
		else {
			pair = new Pair<>(word, null);
		}

		// Construct resulting term.
		return stemTerm(word, true, script);
	}

	/**
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given Buchi automata or null if no such
	 * model exists.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	public Map<Term, Term> testGetResultBuchi(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException, UnsupportedOperationException {
		Pair<NestedLassoWord<MSODAlphabetSymbol>, NestedLassoWord<MSODAlphabetSymbol>> pair;

		// Get the word of the accepted run.
		final NestedLassoWord<MSODAlphabetSymbol> word = getWordBuchi(script, services, automaton);

		// Split word into positive and negative part if the input formula is defined for integer numbers.
		if (mAutomataOperations instanceof MSODAutomataOperationsWeak
				& mFormulaOperations instanceof MSODFormulaOperationsInt) {
			pair = splitWordBuchi(script, word);
		}
		// Input Formula defined only for natural numbers, no negative word exists.
		else {
			pair = new Pair<>(word, null);
		}

		// Construct resulting term.
		// return stemTerm(word, true, script);
		return null;

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

		// Create positive resp. negative LassoWords
		final NestedWord<MSODAlphabetSymbol> loopPos =
				NestedWord.nestedWord(new Word<>((MSODAlphabetSymbol[]) symbolsPosLoop.toArray()));
		final NestedWord<MSODAlphabetSymbol> loopNeg =
				NestedWord.nestedWord(new Word<>((MSODAlphabetSymbol[]) symbolsNegLoop.toArray()));

		lassoWordPos = new NestedLassoWord<>(stemPair.getFirst(), loopPos);
		lassoWordNeg = new NestedLassoWord<>(stemPair.getSecond(), loopNeg);

		return new Pair<>(lassoWordPos, lassoWordNeg);
	}

	/**
	 * Returns a satisfying SMTLIB model for the Weak-MSOD-formula of type Nat represented by the given automata or null
	 * if no such model exists.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	@Deprecated
	public Map<Term, Term> getResultNatWeak(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException, UnsupportedOperationException {

		// Get the word of the acceptedsymbolsPos.toArray() run.
		final NestedWord<MSODAlphabetSymbol> word = getWordWeak(script, services, automaton);

		// Construct resulting term.
		return stemTerm(word, true, script);
	}

	/**
	 * Returns a satisfying SMTLIB model for the Weak-MSOD-formula of type Int represented by the given automata or null
	 * if no such model exists.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	@Deprecated
	public Map<Term, Term> getResultIntWeak(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException, UnsupportedOperationException {
		Map<Term, Term> result = new HashMap<>();
		Map<Term, Term> tmp = new HashMap<>();

		// Get the word of the accepted run.
		final NestedWord<MSODAlphabetSymbol> word = getWordWeak(script, services, automaton);

		final NestedWord<MSODAlphabetSymbol> wordPos =
				(word.length() > 1) ? splitWordWeak(script, word).getFirst() : null;
		final NestedWord<MSODAlphabetSymbol> wordNeg = splitWordWeak(script, word).getSecond();

		// Construct resulting term from positive resp. negative word.
		result = stemTerm(wordNeg, false, script);

		if (wordPos != null) {
			tmp = stemTerm(wordPos, true, script);
		}

		// Build disjunction of all positive and negative parts.
		for (final Term t : tmp.keySet()) {
			if (tmp.get(t) != null) {
				if (result.get(t) != null) {
					result.replace(t, SmtUtils.or(script, result.get(t), tmp.get(t)));
				} else {
					result.replace(t, tmp.get(t));
				}
			}
		}
		return result;
	}

	// TODO:
	@Deprecated
	public Map<Term, Term> getResultNatBuchi(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
		Map<Term, Term> result = new HashMap<>();
		Map<Term, Term> tmp = new HashMap<>();
		final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();

		// Get word of an accepting run and split it into stem and loop.
		final NestedLassoWord<MSODAlphabetSymbol> word = getWordBuchi(script, services, automaton);

		// Create stem and loop conditions.
		result = stemTerm(word.getStem(), true, script);
		tmp = loopTermNat(word.getLoop(), word.getStem().length() - 1, script);

		for (final Term term : terms) {
			if (tmp.get(term) != null) {
				if (result.get(term) != null) {
					result.replace(term, SmtUtils.or(script, result.get(term), tmp.get(term)));
				} else {
					result.replace(term, tmp.get(term));
				}
			}
		}

		return result;
	}

	/**
	 * Return the loop Term condition derived from an accepted LassoWord (for natural numbers only).
	 */
	@Deprecated
	public Map<Term, Term> loopTermNat(final NestedWord<MSODAlphabetSymbol> loop, final int maxStem,
			final Script script) {
		final Map<Term, Term> result = new HashMap<>();
		final Set<Term> terms = loop.getSymbol(0).getTerms();
		final int maxLoop = loop.length();

		for (final Term term : terms) {
			final Set<Term> disjuncts = new HashSet<>();
			Integer value = null;

			// Create new Term variable, with same name as SetOfInt variable but sort IntSort.
			final Term newTerm = term.getTheory().createTermVariable(term.toString(), SmtSortUtils.getIntSort(script));

			// Find all indices that are enabled in the loop, either as a single index or as a part of consecutive
			// enabled indices.
			for (int i = 0; i < loop.length(); i++) {
				// Find Enabled index
				if (loop.getSymbol(i).getMap().get(term)) {
					// Start a new interval
					if (value == null) {
						value = i;
					}
					// Create and store term, if interval cannot be not prolonged.
					if (value != null & (i + 1 == loop.length() || !loop.getSymbol(i + 1).getMap().get(term))) {
						disjuncts.add(createModTermNat(script, newTerm, maxStem, maxLoop, value + 1, i + 1));
						value = null;
					}
				}
			}

			if (!disjuncts.isEmpty()) {
				// Build disjunction of all terms.
				final Term t1 = SmtUtils.or(script, disjuncts);
				// Add conjunct to exclude stem values.
				final Term t2 = SmtUtils.greater(script, newTerm,
						SmtUtils.constructIntValue(script, BigInteger.valueOf(maxStem)));
				result.put(term, SmtUtils.and(script, t1, t2));
			} else {
				result.put(term, null);
			}
		}
		return result;
	}

	public Term createModTermNat(final Script script, final Term term, final int maxStem, final int maxLoop,
			final int start, final int end) {

		// No IntSort variable should have indices enabled in its loop.
		if (SmtSortUtils.isIntSort(term.getSort())) {
			throw new InternalError("Integer representation is corrupted.");
		}

		// "variable % maxLoop"
		final Term mod = SmtUtils.mod(script, term, SmtUtils.constructIntValue(script, BigInteger.valueOf(maxLoop)));

		// If single index is enabled, create binary equality of modulo Term.
		if (start == end) {
			final int value = (start + maxStem) % maxLoop;
			return SmtUtils.binaryEquality(script, mod, SmtUtils.constructIntValue(script, BigInteger.valueOf(value)));
		}
		// Otherwise create a term representing an interval between start and end.
		final Term t1 = SmtUtils.geq(script, mod, SmtUtils.constructIntValue(script, BigInteger.valueOf(start)));
		final Term t2 = SmtUtils.leq(script, mod, SmtUtils.constructIntValue(script, BigInteger.valueOf(end)));

		return SmtUtils.and(script, t1, t2);
	}

	// TODO:
	@Deprecated
	public Map<Term, Term> getResultIntBuchi(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
		final Map<Term, Term> result = new HashMap<>();
		final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();

		// Get word of accepting run and split it into positive / negative stem and loop.
		final NestedLassoWord<MSODAlphabetSymbol> word = getWordBuchi(script, services, automaton);
		final Pair<NestedLassoWord<MSODAlphabetSymbol>, NestedLassoWord<MSODAlphabetSymbol>> pair =
				splitWordBuchi(script, word);
		final NestedWord<MSODAlphabetSymbol> stemPos = pair.getFirst().getStem();
		final NestedWord<MSODAlphabetSymbol> loopPos = pair.getFirst().getLoop();
		final NestedWord<MSODAlphabetSymbol> stemNeg = pair.getSecond().getStem();
		final NestedWord<MSODAlphabetSymbol> loopNeg = pair.getSecond().getLoop();

		return null;
	}

	/**
	 * Returns a Map containing terms and the disjunction corresponding to the numbers encoded in the given stem.
	 */
	@Deprecated
	public Map<Term, Term> stemTerm(final NestedWord<MSODAlphabetSymbol> stem, final Boolean isPositive,
			final Script script) {
		final Map<Term, Term> result = new HashMap<>();
		final Set<Term> terms = stem.getSymbol(0).getTerms();

		for (final Term term : terms) {
			final Set<Term> disjuncts = new HashSet<>();
			Integer value = null;

			// Find all indices that are enabled in the stem, either as a single index or as a part of consecutive
			// enabled indices.
			for (int i = 0; i < stem.length(); i++) {
				// Find Enabled index
				if (stem.getSymbol(i).getMap().get(term)) {
					// Start a new interval
					if (value == null) {
						value = i;
					}
					// Create and store term, if interval cannot be not prolonged.
					if (value != null & (i + 1 == stem.length() || !stem.getSymbol(i + 1).getMap().get(term))) {
						// Convert index to correct number
						if (isPositive) {
							disjuncts.add(createIntervalForStemTerm(script, term, value + 1, i + 1));
						} else {
							disjuncts.add(createIntervalForStemTerm(script, term, -i, -value));
						}
						value = null;
					}
				}
			}

			// Build disjunction of all terms.
			if (!disjuncts.isEmpty()) {
				result.put(term, SmtUtils.or(script, disjuncts));
			} else {
				result.put(term, null);
			}
		}
		return result;
	}

	/**
	 * Create terms needed to describe an integer interval used to represent the stem conditions.
	 */
	@Deprecated
	public Term createIntervalForStemTerm(final Script script, final Term term, final int start, final int end) {
		final Term newTerm = term.getTheory().createTermVariable(term.toString(), SmtSortUtils.getIntSort(script));
		if (start == end) {
			// Return single value if sort of term is IntSort
			if (SmtSortUtils.isIntSort(term.getSort())) {
				return SmtUtils.constructIntValue(script, BigInteger.valueOf(start));
			}
			// Return binary equality if sort is SetOfIntSOrt.
			return SmtUtils.binaryEquality(script, newTerm,
					SmtUtils.constructIntValue(script, BigInteger.valueOf(start)));
		}
		final Term t1 = SmtUtils.constructIntValue(script, BigInteger.valueOf(start));
		final Term t2 = SmtUtils.constructIntValue(script, BigInteger.valueOf(end));
		final Term geq = SmtUtils.geq(script, newTerm, t1);
		final Term leq = SmtUtils.leq(script, newTerm, t2);

		return SmtUtils.and(script, geq, leq);
	}

}