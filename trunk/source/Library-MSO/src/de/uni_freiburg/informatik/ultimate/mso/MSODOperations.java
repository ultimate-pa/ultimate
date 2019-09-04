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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
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
	 * Returns the Int resp. SetOfInt values (natural numbers only) encoded in the given word, represented as a HashMap.
	 */
	public Map<Term, Set<Integer>> getNumbersNat(final Script script, final Set<Term> terms,
			final NestedWord<MSODAlphabetSymbol> word) {

		// Collect all indices at which the value in the word is equal to 1.
		final Map<Term, Set<Integer>> result = new HashMap<>();

		for (final Term term : terms) {
			result.put(term, new HashSet<>());
		}

		for (int i = 0; i < word.length(); i++) {
			final MSODAlphabetSymbol symbol = word.getSymbol(i);
			for (final Entry<Term, Boolean> entry : symbol.getMap().entrySet()) {
				if (entry.getValue()) {
					result.get(entry.getKey()).add(i);
				}
			}
		}
		return result;
	}

	/**
	 * Returns the Int resp. SetOfInt values encoded in the given word, represented as a HashMap.
	 */
	public Map<Term, Set<Integer>> getNumbersInt(final Script script, final Set<Term> terms,
			final NestedWord<MSODAlphabetSymbol> word) {

		// Collect all indices at which the value in the word is equal to 1.
		final Map<Term, Set<Integer>> result = new HashMap<>();

		for (final Term term : terms) {
			result.put(term, new HashSet<>());
		}
		// Compute the number that is represented by the given index.
		for (int i = 0; i < word.length(); i++) {
			final MSODAlphabetSymbol symbol = word.getSymbol(i);
			for (final Entry<Term, Boolean> entry : symbol.getMap().entrySet()) {
				if (entry.getValue()) {
					if (i % 2 == 0) {
						result.get(entry.getKey()).add((int) (-0.5 * i));
					} else {
						result.get(entry.getKey()).add((int) (0.5 * i) + 1);
					}
				}
			}
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
		if (mFormulaOperations instanceof MSODFormulaOperationsNat
				&& mAutomataOperations instanceof MSODAutomataOperationsWeak) {
			return getResultNatWeak(script, services, automaton);
		}
		if (mFormulaOperations instanceof MSODFormulaOperationsNat
				&& mAutomataOperations instanceof MSODAutomataOperationsBuchi) {
			return getResultNatBuchi(script, services, automaton);
		}
		if (mFormulaOperations instanceof MSODFormulaOperationsInt
				&& mAutomataOperations instanceof MSODAutomataOperationsWeak) {
			return getResultIntWeak(script, services, automaton);
		}
		if (mFormulaOperations instanceof MSODFormulaOperationsInt
				&& mAutomataOperations instanceof MSODAutomataOperationsBuchi) {
			return getResultIntBuchi(script, services, automaton);
		}
		return null;
	}

	/**
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given automata or null if no such model
	 * exists. Should only be used with finite automata and MSOD-formulas on Natural Numbers.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	public Map<Term, Term> getResultNatWeak(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
		final Map<Term, Term> result = new HashMap<>();
		final NestedWord<MSODAlphabetSymbol> word = getWordWeak(script, services, automaton);

		if (word != null) {

			// TODO: Deal with empty model in case no free variable exists in the formula.

			if (automaton.getAlphabet().isEmpty()) {
				// TODO: Deal with empty alphabet.
			}
			final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();

			// Get all numbers that are encoded in the word.
			final Map<Term, Set<Integer>> numbers = getNumbersNat(script, terms, word);

			// Construct result term.
			for (final Term term : terms) {
				Term stemTerm = null;

				// Deal with variables of type Int.
				if (SmtSortUtils.isIntSort(term.getSort())) {
					if (numbers.get(term).size() != 1) {
						throw new UnsupportedOperationException("This is not a valid Integer representation!");
					}
					// Construct a term that represents the according Int value.
					final Term value =
							SmtUtils.constructIntValue(script, BigInteger.valueOf(numbers.get(term).iterator().next()));
					result.put(term, value);

					// Deal with variables of type SetOfInt.
				} else {
					final Term setTerm = script.variable(term.toString(), SmtSortUtils.getIntSort(script));
					final Iterator<Integer> itStem = numbers.get(term).iterator();

					// Construct a term for each element in the set and build a disjunction of the form
					// "(variableName = value1) or (variableName = value2) or ... ".
					while (itStem.hasNext()) {
						final Term value = SmtUtils.constructIntValue(script, BigInteger.valueOf(itStem.next()));
						final Term eqTerm = SmtUtils.binaryEquality(script, setTerm, value);
						if (stemTerm == null) {
							stemTerm = eqTerm;
						}
						stemTerm = SmtUtils.or(script, eqTerm, stemTerm);
					}

					// In case of an empty set, the condition for an element to be in the set is set to "false".
					if (stemTerm == null) {
						result.put(term, term.getTheory().mFalse);
					} else {
						result.put(term, stemTerm);
					}
				}
			}
		}
		return result;
	}

	/**
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given automata or null if no such model
	 * exists. Should only be used with finite automata and MSOD-formulas on Integer Numbers.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	public Map<Term, Term> getResultIntWeak(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
		final Map<Term, Term> result = new HashMap<>();
		final NestedWord<MSODAlphabetSymbol> word = getWordWeak(script, services, automaton);

		if (word != null) {

			// TODO: Deal with empty model in case no free variable exists in the formula.

			if (automaton.getAlphabet().isEmpty()) {
				// TODO: Deal with empty alphabet.
			}
			final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();

			// Get all numbers that are encoded in the word.
			final Map<Term, Set<Integer>> numbers = getNumbersInt(script, terms, word);

			// Construct result term.
			for (final Term term : terms) {
				Term stemTerm = null;

				// Deal with variables of type Int.
				if (SmtSortUtils.isIntSort(term.getSort())) {
					if (numbers.get(term).size() != 1) {
						throw new UnsupportedOperationException("This is not a valid Integer representation!");
					}
					// Construct a term that represents the according Int value.
					final Term value =
							SmtUtils.constructIntValue(script, BigInteger.valueOf(numbers.get(term).iterator().next()));
					result.put(term, value);

					// Deal with variables of type SetOfInt.
				} else {
					final Term setTerm = script.variable(term.toString(), SmtSortUtils.getIntSort(script));
					final Iterator<Integer> itStem = numbers.get(term).iterator();

					// Construct a term for each element in the set and build a disjunction of the form
					// "(variableName = value1) or (variableName = value2) or ... ".
					while (itStem.hasNext()) {
						final Term value = SmtUtils.constructIntValue(script, BigInteger.valueOf(itStem.next()));
						final Term eqTerm = SmtUtils.binaryEquality(script, setTerm, value);
						if (stemTerm == null) {
							stemTerm = eqTerm;
						}
						stemTerm = SmtUtils.or(script, eqTerm, stemTerm);
					}

					// In case of an empty set, the condition for an element to be in the set is set to "false".
					if (stemTerm == null) {
						result.put(term, term.getTheory().mFalse);
					} else {
						result.put(term, stemTerm);
					}
				}
			}
		}
		return result;
	}

	/**
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given automata or null if no such model
	 * exists. Should only be used with Büchi automata and MSOD-formulas on Natural Number.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	public Map<Term, Term> getResultNatBuchi(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
		final Map<Term, Term> result = new HashMap<>();
		final NestedLassoWord<MSODAlphabetSymbol> word = getWordBuchi(script, services, automaton);

		if (word != null) {
			// TODO: Deal with empty model in case no free variable exists in the formula.
			if (word.getStem().getSymbol(0).toString() == "empty"
					|| word.getLoop().getSymbol(0).toString() == "empty") {
				throw new UnsupportedOperationException("EMPTY");
			}
			if (automaton.getAlphabet().isEmpty()) {
				// TODO: Deal with empty alphabet.
			}
			final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();
			final NestedWord<MSODAlphabetSymbol> stem = word.getStem();
			final NestedWord<MSODAlphabetSymbol> loop = word.getLoop();

			// Get all numbers that are encoded in the stem resp. loop of the lassoword.
			final Map<Term, Set<Integer>> stemIndices = getNumbersNat(script, terms, stem);
			final Map<Term, Set<Integer>> loopIndices = getNumbersNat(script, terms, loop);

			// Construct result term.
			for (final Term term : terms) {
				Term stemTerm = null;
				Term loopTerm = null;

				// Deal with variables of type Int.
				if (SmtSortUtils.isIntSort(term.getSort())) {
					if (stemIndices.get(term).size() != 1 || loopIndices.get(term).size() != 0) {
						throw new UnsupportedOperationException("This is not a valid Integer representation!");
					}
					// Construct a term that represents the according Int value.
					final Term value = SmtUtils.constructIntValue(script,
							BigInteger.valueOf(stemIndices.get(term).iterator().next()));
					result.put(term, value);

					// Deal with variables of type SetOfInt.
				} else {
					final Term setTerm = script.variable(term.toString(), SmtSortUtils.getIntSort(script));
					final Term resultTerm = null;
					final Iterator<Integer> itStem = stemIndices.get(term).iterator();
					final Iterator<Integer> itLoop = loopIndices.get(term).iterator();

					// Construct a term for each element in the set encoded in the stem and build a disjunction of the
					// form "(variableName = value1) or (variableName = value2) or ... ".
					while (itStem.hasNext()) {
						final Term value = SmtUtils.constructIntValue(script, BigInteger.valueOf(itStem.next()));
						final Term eqTerm = SmtUtils.binaryEquality(script, setTerm, value);
						if (stemTerm == null) {
							stemTerm = eqTerm;
						}
						stemTerm = SmtUtils.or(script, eqTerm, stemTerm);
					}

					final int stemLength = stem.length();
					final int maxLoopIndex = Collections.max(loopIndices.get(term));

					// Calculate representation of numbers in the loop based on the length of the stem.
					final Term minusTerm = SmtUtils.minus(script, setTerm,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(stemLength - 1)));
					final Term greaterTerm =
							SmtUtils.greater(script, minusTerm, SmtUtils.constructIntValue(script, BigInteger.ZERO));
					final Term modTerm = SmtUtils.mod(script, minusTerm,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(maxLoopIndex + 1)));

					// Construct term to represent conditions for numbers encoded in the loop.
					while (itLoop.hasNext()) {
						result.put(term, resultTerm);
						loopTerm = SmtUtils.and(script, greaterTerm,
								SmtUtils.binaryEquality(script, modTerm, SmtUtils.constructIntValue(script,
										BigInteger.valueOf((itLoop.next() + 1) % (maxLoopIndex + 1)))));
					}

					// Deal with all combinations of possibly empty Terms
					if (stemTerm != null && loopTerm != null) {
						result.put(term, SmtUtils.or(script, stemTerm, loopTerm));
					} else if (stemTerm == null) {
						result.put(term, loopTerm);
					} else if (loopTerm == null) {
						result.put(term, stemTerm);
					} else {
						// In case of an empty set, the condition for an element to be in the set is set to "false".
						result.put(term, term.getTheory().mFalse);
					}
				}
			}
		}
		return result;
	}

	/**
	 * Returns a satisfying SMTLIB model for the MSOD-formula represented by the given automata or null if no such model
	 * exists. Should only be used with Büchi automata and MSOD-formulas on Integer Number.
	 *
	 * @throws AutomataLibraryException
	 * @throws UnsupportedOperationException
	 *             if representation of Integer variable is corrupted
	 */
	public Map<Term, Term> getResultIntBuchi(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {
		final Map<Term, Term> result = new HashMap<>();
		final NestedLassoWord<MSODAlphabetSymbol> word = getWordBuchi(script, services, automaton);

		if (word != null) {

			// TODO: Deal with empty model in case no free variable exists in the formula.

			if (automaton.getAlphabet().isEmpty()) {
				// TODO: Deal with empty alphabet.
			}
			final Set<Term> terms = automaton.getAlphabet().iterator().next().getTerms();
			final NestedWord<MSODAlphabetSymbol> stem = word.getStem();
			NestedWord<MSODAlphabetSymbol> loop = word.getLoop();

			// Deal with odd loop length by unfolding the loop once (as an odd loop length causes a change in sign!).
			if (loop.length() % 2 == 1) {
				loop = loop.concatenate(loop);
			}

			// Get all numbers that are encoded in the stem resp. loop of the lassoword.
			final Map<Term, Set<Integer>> stemNumbers = getNumbersInt(script, terms, stem);
			Map<Term, Set<Integer>> loopNumbers = getNumbersInt(script, terms, loop);
			final Map<Term, Set<Integer>> tempMap = new HashMap<>();

			// Deal with odd stem length as this changes the order in the loop.
			if (stem.length() % 2 == 1) {
				// Correct the numbers encoded in the loop according to changed order.
				for (final Term term : terms) {
					final Iterator<Integer> it = loopNumbers.get(term).iterator();
					final Set<Integer> tempSet = new HashSet<>();

					while (it.hasNext()) {
						final int value = -(it.next().intValue() - 1);
						tempSet.add(value);
					}
					tempMap.put(term, tempSet);
				}
				loopNumbers = tempMap;
			}

			// Construct result term.
			for (final Term term : terms) {
				Term stemTerm = null;
				Term loopTerm = null;

				// Deal with variables of type Int.
				if (SmtSortUtils.isIntSort(term.getSort())) {
					if (stemNumbers.get(term).size() != 1 || loopNumbers.get(term).size() != 0) {
						throw new UnsupportedOperationException("This is not a valid Integer representation!");
					}
					// Construct a term that represents the according Int value.
					final Term value = SmtUtils.constructIntValue(script,
							BigInteger.valueOf(stemNumbers.get(term).iterator().next()));
					result.put(term, value);

					// Deal with variables of type SetOfInt.
				} else {
					final Term setTerm = script.variable(term.toString(), SmtSortUtils.getIntSort(script));
					final Iterator<Integer> itStem = stemNumbers.get(term).iterator();
					final Iterator<Integer> itLoop = loopNumbers.get(term).iterator();

					// Construct a term for each element in the set encoded in the stem and build a disjunction of the
					// form "(variableName = value1) or (variableName = value2) or ... ".
					while (itStem.hasNext()) {
						final Term value = SmtUtils.constructIntValue(script, BigInteger.valueOf(itStem.next()));
						final Term eqTerm = SmtUtils.binaryEquality(script, setTerm, value);
						if (stemTerm == null) {
							stemTerm = eqTerm;
						}
						stemTerm = SmtUtils.or(script, eqTerm, stemTerm);
					}

					// Compute number of positive resp. negative numbers in stem.
					int stemNumberPos;
					int stemNumberNeg;
					if (stem.length() % 2 == 1) {
						stemNumberPos = (int) (0.5 * (stem.length() - 1));
						stemNumberNeg = -stemNumberPos;
					} else {
						stemNumberPos = (int) (0.5 * stem.length());
						stemNumberNeg = -stemNumberPos + 1;
					}

					// Get the min resp. max values of the loop.
					final int maxLoopNumber = Collections.max(loopNumbers.get(term));
					final int minLoopNumber = Collections.max(loopNumbers.get(term));

					// Calculate representation of numbers in the loop based on the length of the stem.
					final Term minusTermPos = SmtUtils.minus(script, setTerm,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(stemNumberPos)));
					final Term minusTermNeg = SmtUtils.minus(script, setTerm,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(stemNumberNeg)));
					final Term greaterTermPos =
							SmtUtils.greater(script, minusTermPos, SmtUtils.constructIntValue(script, BigInteger.ZERO));
					final Term lessTermNeg =
							SmtUtils.less(script, minusTermNeg, SmtUtils.constructIntValue(script, BigInteger.ZERO));
					final Term modTermPos = SmtUtils.mod(script, minusTermPos,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(maxLoopNumber)));
					final Term modTermNeg = SmtUtils.mod(script, minusTermNeg,
							SmtUtils.constructIntValue(script, BigInteger.valueOf(Math.abs(minLoopNumber))));

					// Construct term for set condition depending on the sign of the number.
					while (itLoop.hasNext()) {
						final int value = itLoop.next();
						Term t = null;
						if (value > 0) {
							t = SmtUtils.and(script, greaterTermPos,
									SmtUtils.binaryEquality(script, modTermPos, SmtUtils.constructIntValue(script,
											BigInteger.valueOf((value + 1) % (maxLoopNumber)))));
						} else {
							t = SmtUtils.and(script, lessTermNeg,
									SmtUtils.binaryEquality(script, modTermNeg, SmtUtils.constructIntValue(script,
											BigInteger.valueOf((value + 1) % (Math.abs(minLoopNumber))))));
						}
						if (loopTerm != null) {
							loopTerm = SmtUtils.or(script, loopTerm, t);
						} else {
							loopTerm = t;
						}
					}

					// Deal with all combinations of possibly empty Terms
					if (stemTerm != null && loopTerm != null) {
						result.put(term, SmtUtils.or(script, stemTerm, loopTerm));
					} else if (stemTerm == null) {
						result.put(term, loopTerm);
					} else if (loopTerm == null) {
						result.put(term, stemTerm);
					} else {
						// In case of an empty set, the condition for an element to be in the set is set to "false".
						result.put(term, term.getTheory().mFalse);
					}
				}
			}
		}
		return result;
	}
}