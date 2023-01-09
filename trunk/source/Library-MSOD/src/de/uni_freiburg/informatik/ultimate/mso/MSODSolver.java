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
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class provides methods to construct and manipulate automata that correspond to MSOD-Formulas.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public final class MSODSolver {

	public enum MSODLogic {
		MSODInt, MSODNat, MSODIntWeak, MSODNatWeak,
	}

	private final Script mScript;
	private final ILogger mLogger;
	private final AutomataLibraryServices mAutomataLibrarayServices;
	private final MSODFormulaOperations mFormulaOperations;
	private final MSODAutomataOperations mAutomataOperations;

	public MSODSolver(final IUltimateServiceProvider services, final Script script, final ILogger logger,
			final MSODLogic logic) {

		mScript = script;
		mLogger = logger;
		mAutomataLibrarayServices = new AutomataLibraryServices(services);

		switch (logic) {
		case MSODNatWeak:
			mFormulaOperations = new MSODFormulaOperationsNat();
			mAutomataOperations = new MSODAutomataOperationsWeak();
			break;
		case MSODIntWeak:
			mFormulaOperations = new MSODFormulaOperationsInt();
			mAutomataOperations = new MSODAutomataOperationsWeak();
			break;
		case MSODNat:
			mFormulaOperations = new MSODFormulaOperationsNat();
			mAutomataOperations = new MSODAutomataOperationsBuchi();
			break;
		case MSODInt:
			mFormulaOperations = new MSODFormulaOperationsInt();
			mAutomataOperations = new MSODAutomataOperationsBuchi();
			break;
		default:
			throw new IllegalArgumentException("Unknown logic: " + logic);
		}
	}

	/**
	 * Returns a string representation of the given automaton. (only for debugging)
	 */
	public String automatonToString(final IAutomaton<?, ?> automaton, final Format format) {
		return AutomatonDefinitionPrinter.toString(mAutomataLibrarayServices, "", automaton);
	}

	/**
	 * Traverses term in post order.
	 *
	 * @throws Exception
	 *
	 * @throws AutomataLibraryException
	 *             iff π = 4.
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> traversePostOrder(final Term term)
			throws AutomataLibraryException {
		mLogger.info("Traverse term: " + term);

		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;

			if (quantifiedFormula.getQuantifier() == QuantifiedFormula.FORALL) {
				return processForall(quantifiedFormula);
			}

			if (quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS) {
				return processExists(quantifiedFormula);
			}
		}

		if (term instanceof ApplicationTerm) {
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			final String functionSymbol = applicationTerm.getFunction().getName();

			if (functionSymbol.equals("true")) {
				return processTrue();
			}

			if (functionSymbol.equals("false")) {
				return processFalse();
			}

			if (functionSymbol.equals("not")) {
				return processNegation(applicationTerm);
			}

			if (functionSymbol.equals("and")) {
				return processConjunction(applicationTerm);
			}

			if (functionSymbol.equals("or")) {
				return processDisjunction(applicationTerm);
			}

			if (functionSymbol.equals("=>")) {
				return processImplication(applicationTerm);
			}

			if (functionSymbol.equals("strictSubsetInt")) {
				return processStrictSubset(applicationTerm);
			}

			if (functionSymbol.equals("subsetInt")) {
				return processSubset(applicationTerm);
			}

			if (functionSymbol.equals("element")) {
				return processElement(applicationTerm);
			}

			if (functionSymbol.equals("=")) {
				return processEqual(applicationTerm);
			}

			if (functionSymbol.equals(">")) {
				return processGreater(applicationTerm);
			}

			if (functionSymbol.equals(">=")) {
				return processGreaterEqual(applicationTerm);
			}

			if (functionSymbol.equals("<") || functionSymbol.equals("<=")) {
				return processLessOrLessEqual(applicationTerm);
			}
		}

		throw new IllegalArgumentException("Input must be a QuantifiedFormula or an ApplicationTerm.");
	}

	/**
	 * Returns automaton that represents "∀ φ". Performs equivalent transformation to "¬∃ ¬φ" and calls
	 * {@link #traversePostOrder(Term)} with the result.
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processForall(final QuantifiedFormula term)
			throws AutomataLibraryException {

		final Term exists = SmtUtils.not(mScript, mScript.quantifier(QuantifiedFormula.EXISTS, term.getVariables(),
				SmtUtils.not(mScript, term.getSubformula())));

		return traversePostOrder(exists);
	}

	/**
	 * Returns automaton that represents "∃ φ".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processExists(final QuantifiedFormula term)
			throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getSubformula());
		mLogger.info("Construct ∃ φ: " + term);

		// Get free variables and constants.
		final List<Term> freeVariables = new ArrayList<>(Arrays.asList(term.getFreeVars()));
		freeVariables.addAll((SmtUtils.extractConstants(term, true)));

		// Project automaton onto free variables.
		final Set<MSODAlphabetSymbol> alphabet = MSODUtils.createAlphabet(freeVariables);
		result = MSODAutomataOperations.project(mAutomataLibrarayServices, result, alphabet, false);

		// Saturate language of automaton such that it accepts words introduced by projection.
		final MSODAlphabetSymbol zero = new MSODAlphabetSymbol(freeVariables, false);
		result = MSODAutomataOperations.saturate(mAutomataLibrarayServices, result, zero);

		return result;
	}

	/**
	 * Returns automaton that represents "true".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processTrue() {
		mLogger.info("Construct true");

		return MSODFormulaOperations.trueAutomaton(mAutomataLibrarayServices);
	}

	/**
	 * Returns automaton that represents "false".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processFalse() {
		mLogger.info("Construct false");

		return MSODFormulaOperations.falseAutomaton(mAutomataLibrarayServices);
	}

	/**
	 * Returns automaton that represents "¬φ".
	 *
	 * @throws Exception
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processNegation(final ApplicationTerm term)
			throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct not φ: " + term);

		result = mAutomataOperations.complement(mAutomataLibrarayServices, result);

		return result;
	}

	/**
	 * Returns automaton that represents "φ ∧ ... ∧ ψ".
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Intersect} fails.
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processConjunction(final ApplicationTerm term)
			throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct φ and ψ (0): " + term);

		for (int i = 1; i < term.getParameters().length; i++) {
			INestedWordAutomaton<MSODAlphabetSymbol, String> tmp = traversePostOrder(term.getParameters()[i]);
			mLogger.info("Construct φ and ψ (" + i + "): " + term);

			final Set<MSODAlphabetSymbol> symbols = MSODUtils.mergeAlphabets(result.getAlphabet(), tmp.getAlphabet());

			result = MSODAutomataOperations.project(mAutomataLibrarayServices, result, symbols, true);
			tmp = MSODAutomataOperations.project(mAutomataLibrarayServices, tmp, symbols, true);

			result = mAutomataOperations.intersect(mAutomataLibrarayServices, result, tmp);
		}

		return result;
	}

	/**
	 * Returns automaton that represents "φ ∨ ... ∨ ψ". Performs equivalent transformation to conjunction and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processDisjunction(final ApplicationTerm term)
			throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct φ and ψ (0): " + term);

		for (int i = 1; i < term.getParameters().length; i++) {
			INestedWordAutomaton<MSODAlphabetSymbol, String> tmp = traversePostOrder(term.getParameters()[i]);
			mLogger.info("Construct φ and ψ (" + i + "): " + term);

			final Set<MSODAlphabetSymbol> symbols = MSODUtils.mergeAlphabets(result.getAlphabet(), tmp.getAlphabet());

			result = MSODAutomataOperations.project(mAutomataLibrarayServices, result, symbols, true);
			tmp = MSODAutomataOperations.project(mAutomataLibrarayServices, tmp, symbols, true);

			result = mAutomataOperations.union(mAutomataLibrarayServices, result, tmp);
		}

		return result;
	}

	/**
	 * Returns automaton that represents "φ ⇒ ψ". Performs equivalent transformation to "¬φ ∧ ψ" and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processImplication(final ApplicationTerm term)
			throws AutomataLibraryException {

		final Term[] terms = term.getParameters();
		for (int i = 0; i < terms.length - 1; i++) {
			terms[i] = SmtUtils.not(mScript, terms[i]);
		}

		return traversePostOrder(SmtUtils.or(mScript, terms));
	}

	/**
	 * Returns automaton that represents "t = c". Performs equivalent transformation to "(t <= c) ∧ ¬(t < c)" and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processEqual(final ApplicationTerm term)
			throws AutomataLibraryException {

		for (final Term t : term.getParameters()) {
			mLogger.error("TERM: " + t);
		}

		final Term[] terms = term.getParameters();
		final Term lessEqual = SmtUtils.leq(mScript, terms[0], terms[1]);
		// This term should not be simplified, therefore we use mScript.term("not", ...) instead of SmtUtils.not
		final Term greaterEqual = mScript.term("not", SmtUtils.less(mScript, terms[0], terms[1]));
		final Term equal = SmtUtils.and(mScript, lessEqual, greaterEqual);

		mLogger.error("equal: " + equal);

		return traversePostOrder(equal);
	}

	/**
	 * Returns automaton that represents "t > c". Performs equivalent transformation to "¬(t <= c)" and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processGreater(final ApplicationTerm term)
			throws AutomataLibraryException {

		final Term[] terms = term.getParameters();
		final Term greater = SmtUtils.not(mScript, SmtUtils.leq(mScript, terms[0], terms[1]));

		return traversePostOrder(greater);
	}

	/**
	 * Returns automaton that represents "t >= c". Performs equivalent transformation to "¬(t < c)" and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processGreaterEqual(final ApplicationTerm term)
			throws AutomataLibraryException {

		final Term[] terms = term.getParameters();
		final Term greaterEqual = SmtUtils.not(mScript, SmtUtils.less(mScript, terms[0], terms[1]));

		return traversePostOrder(greaterEqual);
	}

	/**
	 * Returns automaton that represents "t < c" or "t <= c".
	 *
	 * @throws AutomataLibraryException
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processLessOrLessEqual(final ApplicationTerm term)
			throws AutomataLibraryException {

		final PolynomialRelation polyRel = PolynomialRelation.of(mScript, term, TransformInequality.NONSTRICT2STRICT);
		final AffineTerm affineTerm = (AffineTerm) polyRel.getPolynomialTerm();
		final Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		final Rational constant = affineTerm.getConstant().negate();

		if (variables.size() == 1) {
			final Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (var.getValue().equals(Rational.ONE)) {
				mLogger.info("Construct x < c: " + term);
				return mFormulaOperations.strictIneqAutomaton(mAutomataLibrarayServices, var.getKey(), constant);
			}

			if (var.getValue().equals(Rational.MONE)) {
				mLogger.info("Construct -x < c: " + term);
				return mFormulaOperations.strictNegIneqAutomaton(mAutomataLibrarayServices, var.getKey(), constant);
			}
		}

		if (variables.size() == 2) {
			mLogger.info("Construct x-y < c: " + term);

			final Iterator<Entry<Term, Rational>> it = variables.entrySet().iterator();
			final Entry<Term, Rational> var1 = it.next();
			final Entry<Term, Rational> var2 = it.next();

			if (!var1.getValue().add(var2.getValue()).equals(Rational.ZERO)) {
				throw new IllegalArgumentException("Input is not difference logic.");
			}

			if (var1.getValue().equals(Rational.ONE)) {
				mLogger.error("x: " + var1.getKey() + ", y: " + var2.getKey() + ", c: " + constant);
				return mFormulaOperations.strictIneqAutomaton(mAutomataLibrarayServices, var1.getKey(), var2.getKey(),
						constant);
			}

			if (var2.getValue().equals(Rational.ONE)) {
				mLogger.error("x: " + var2.getKey() + ", y: " + var1.getKey() + ", c: " + constant);
				return mFormulaOperations.strictIneqAutomaton(mAutomataLibrarayServices, var2.getKey(), var1.getKey(),
						constant);
			}
		}

		throw new IllegalArgumentException("Invalid inequality");
	}

	/**
	 * Returns automaton that represents "X ⊊ Y".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processStrictSubset(final ApplicationTerm term) {
		mLogger.info("Construct X strictSubset Y: " + term);

		if (term.getParameters().length != 2) {
			throw new IllegalArgumentException("StrictSubset must have exactly two parameters.");
		}

		return mFormulaOperations.strictSubsetAutomaton(mAutomataLibrarayServices, term.getParameters()[0],
				term.getParameters()[1]);
	}

	/**
	 * Returns automaton that represents "X ⊆ Y".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processSubset(final ApplicationTerm term) {
		mLogger.info("Construct X subset Y: " + term);

		if (term.getParameters().length != 2) {
			throw new IllegalArgumentException("Subset must have exactly two parameters.");
		}

		return mFormulaOperations.subsetAutomaton(mAutomataLibrarayServices, term.getParameters()[0],
				term.getParameters()[1]);
	}

	/**
	 * Returns automaton that represents "t ∈ X".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processElement(final ApplicationTerm term)
			throws AutomataLibraryException {

		if (term.getParameters().length != 2) {
			throw new IllegalArgumentException("Element must have exactly two parameters.");
		}

		final AffineTerm affineTerm =
				(AffineTerm) new AffineTermTransformer(mScript).transform(term.getParameters()[0]);

		if (affineTerm.isErrorTerm()) {
			throw new IllegalArgumentException("Could not create AffineTerm.");
		}

		final Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		final Rational constant = affineTerm.getConstant();

		if (variables.size() == 0) {
			mLogger.info("Construct c element X: " + term);
			return mFormulaOperations.constElementAutomaton(mAutomataLibrarayServices, constant,
					term.getParameters()[1]);
		}

		if (variables.size() == 1) {
			mLogger.info("Construct x+c element Y: " + term);
			final Entry<Term, Rational> variable = variables.entrySet().iterator().next();

			if (!variable.getValue().equals(Rational.ONE)) {
				throw new IllegalArgumentException("Invalid input.");
			}

			return mFormulaOperations.elementAutomaton(mAutomataLibrarayServices, variable.getKey(), constant,
					term.getParameters()[1]);
		}

		throw new IllegalArgumentException("Invalid input.");
	}

	/**
	 *
	 */
	public Map<Term, Term> getResult(final Script script, final ILogger logger, final AutomataLibraryServices services,
			final Term term) throws AutomataLibraryException {

		final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton = traversePostOrder(term);
		mLogger.info(MSODUtils.automatonToString(mAutomataLibrarayServices, automaton));
		mLogger.info("info: " + automaton.sizeInformation());

		NestedLassoWord<MSODAlphabetSymbol> word = mAutomataOperations.getWord(services, automaton);

		if (word == null) {
			return null;
		}

		// Unfold loop once if loop length is odd.
		if (mFormulaOperations instanceof MSODFormulaOperationsInt && word.getLoop().length() % 2 != 0) {
			word = new NestedLassoWord<>(word.getStem(), word.getLoop().concatenate(word.getLoop()));
		}
		logger.info("Word: " + word);

		final Map<Term, List<Integer>> stem = mFormulaOperations.wordToNumbers(word.getStem(), 0);
		final Map<Term, List<Integer>> loop = mFormulaOperations.wordToNumbers(word.getLoop(), word.getStem().length());

		final int stemLength = word.getStem().length();
		final int loopLength = mFormulaOperations instanceof MSODFormulaOperationsInt ? word.getLoop().length() / 2
				: word.getLoop().length();

		final Pair<Integer, Integer> stemBounds = mFormulaOperations.stemBounds(stemLength);

		final Map<Term, Term> results = new HashMap<>();
		for (final Term key : stem.keySet()) {
			results.put(key, SmtUtils.or(script, MSODFormulaOperations.stemResult(script, key, stem.get(key)),
					MSODFormulaOperations.loopResult(script, key, loop.get(key), stemBounds, loopLength)));
		}

		return results;
	}
}