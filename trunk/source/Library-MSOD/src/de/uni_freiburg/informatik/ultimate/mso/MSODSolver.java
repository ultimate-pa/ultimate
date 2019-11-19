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

import java.lang.reflect.Array;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AbstractGeneralizedAffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.NotAffineException;
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

	Script mScript;
	private final ILogger mLogger;
	private final AutomataLibraryServices mAutomataLibrarayServices;
	private final MSODFormulaOperations mFormulaOperations;
	private final MSODAutomataOperations mAutomataOperations;

	public MSODSolver(final IUltimateServiceProvider services, final Script script, final ILogger logger,
			final MSODFormulaOperations formulaOperations, final MSODAutomataOperations automataOperations) {

		mScript = script;
		mLogger = logger;
		mAutomataLibrarayServices = new AutomataLibraryServices(services);
		mFormulaOperations = formulaOperations;
		mAutomataOperations = automataOperations;
	}

	/**
	 * Returns a string representation of the given automaton. (only for debugging)
	 */
	public String automatonToString(final IAutomaton<?, ?> automaton, final Format format) {
		AutomatonDefinitionPrinter<?, ?> printer;
		printer = new AutomatonDefinitionPrinter<>(mAutomataLibrarayServices, "", Format.ATS, automaton);

		return printer.getDefinitionAsString();
	}

	/**
	 * Traverses term in post order.
	 *
	 * @throws AutomataLibraryException
	 *             iff π = 4.
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> traversePostOrder(final Term term) throws Exception {
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
	 * Returns automaton that represents "∀ φ". Performs equivalent transformation to ¬∃ ¬φ and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processForall(final QuantifiedFormula term)
			throws Exception {

		final Term exists = SmtUtils.not(mScript, mScript.quantifier(QuantifiedFormula.EXISTS, term.getVariables(),
				SmtUtils.not(mScript, term.getSubformula())));

		return traversePostOrder(exists);
	}

	/**
	 * Returns automaton that represents "∃ φ".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processExists(final QuantifiedFormula term)
			throws Exception {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getSubformula());
		mLogger.info("Construct ∃ φ: " + term);

		// Get free variables and constants.
		final List<Term> freeVariables = new ArrayList<>(Arrays.asList(term.getFreeVars()));
		freeVariables.addAll((new ConstantFinder()).findConstants(term, true));

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
	 * Returns automaton that represents "not φ".
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Complement} or {@link Intersect} fails.
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processNegation(final ApplicationTerm term)
			throws AutomataLibraryException, Exception {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct not φ: " + term);

		result = mAutomataOperations.complement(mAutomataLibrarayServices, result);

		mLogger.error(result);

		return result;
	}

	/**
	 * Returns automaton that represents "φ and ... and ψ".
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Intersect} fails.
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processConjunction(final ApplicationTerm term)
			throws AutomataLibraryException, Exception {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct φ and ψ (0): " + term);

		for (int i = 1; i < term.getParameters().length; i++) {
			INestedWordAutomaton<MSODAlphabetSymbol, String> tmp = traversePostOrder(term.getParameters()[i]);
			mLogger.info("Construct φ and ψ (" + i + "): " + term);

			Set<MSODAlphabetSymbol> symbols;
			symbols = MSODUtils.mergeAlphabets(result.getAlphabet(), tmp.getAlphabet());

			result = MSODAutomataOperations.project(mAutomataLibrarayServices, result, symbols, true);
			tmp = MSODAutomataOperations.project(mAutomataLibrarayServices, tmp, symbols, true);

			result = mAutomataOperations.intersect(mAutomataLibrarayServices, result, tmp);
		}

		return result;
	}

	/**
	 * Returns automaton that represents "φ or ... or ψ". Performs equivalent transformation to conjunction and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processDisjunction(final ApplicationTerm term)
			throws Exception {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct φ and ψ (0): " + term);

		for (int i = 1; i < term.getParameters().length; i++) {
			INestedWordAutomaton<MSODAlphabetSymbol, String> tmp = traversePostOrder(term.getParameters()[i]);
			mLogger.info("Construct φ and ψ (" + i + "): " + term);

			Set<MSODAlphabetSymbol> symbols;
			symbols = MSODUtils.mergeAlphabets(result.getAlphabet(), tmp.getAlphabet());

			result = MSODAutomataOperations.project(mAutomataLibrarayServices, result, symbols, true);
			tmp = MSODAutomataOperations.project(mAutomataLibrarayServices, tmp, symbols, true);

			result = mAutomataOperations.union(mAutomataLibrarayServices, result, tmp);
		}

		return result;
	}

	/**
	 * Returns automaton that represents "φ implies ψ". Performs equivalent transformation to "not φ and ψ" and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processImplication(final ApplicationTerm term)
			throws Exception {

		final Term[] terms = term.getParameters();
		for (int i = 0; i < terms.length - 1; i++) {
			terms[i] = SmtUtils.not(mScript, terms[i]);
		}

		return traversePostOrder(SmtUtils.or(mScript, terms));
	}

	/**
	 * Returns automaton that represents "t = c". Performs equivalent transformation to "t <= c and not t < c" and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processEqual(final ApplicationTerm term) throws Exception {

		for (final Term t : term.getParameters()) {
			mLogger.error("TERM: " + t);
		}

		final Term[] terms = term.getParameters();
		final Term lessEqual = SmtUtils.leq(mScript, terms[0], terms[1]);
		final Term greaterEqual = SmtUtils.not(mScript, SmtUtils.less(mScript, terms[0], terms[1]));
		final Term equal = SmtUtils.and(mScript, lessEqual, greaterEqual);

		mLogger.error("equal: " + equal);

		return traversePostOrder(equal);
	}

	/**
	 * Returns automaton that represents "t > c". Performs equivalent transformation to "not t <= c" and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processGreater(final ApplicationTerm term)
			throws Exception {

		final Term[] terms = term.getParameters();
		final Term greater = SmtUtils.not(mScript, SmtUtils.leq(mScript, terms[0], terms[1]));

		return traversePostOrder(greater);
	}

	/**
	 * Returns automaton that represents "t >= c". Performs equivalent transformation to "not t < c" and calls
	 * {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processGreaterEqual(final ApplicationTerm term)
			throws Exception {

		final Term[] terms = term.getParameters();
		final Term greaterEqual = SmtUtils.not(mScript, SmtUtils.less(mScript, terms[0], terms[1]));

		return traversePostOrder(greaterEqual);
	}

	/**
	 * Returns automaton that represents "t < c" or "t <= c".
	 *
	 * @throws NotAffineException
	 *             if construction of {@link AffineRelation} fails.
	 *
	 * @throws AutomataLibraryException
	 */
	private INestedWordAutomaton<MSODAlphabetSymbol, String> processLessOrLessEqual(final ApplicationTerm term)
			throws NotAffineException, AutomataLibraryException {

		final AffineRelation affineRelation =
				AffineRelation.convert(mScript, term, TransformInequality.NONSTRICT2STRICT);
		final AffineTerm affineTerm = affineRelation.getAffineTerm();
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
	 * Returns automaton that represents "X strictSubset Y".
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
	 * Returns automaton that represents "X subset Y".
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
	 * Returns automaton that represents "t element X".
	 *
	 * @throws AutomataLibraryException
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
	 * Returns a {@link NestedWord} accepted by the given automaton, or null if language of automaton is empty.
	 *
	 * @throws AutomataLibraryException
	 *             if {@link IsEmpty} fails
	 */
	public static NestedWord<MSODAlphabetSymbol> getWordWeak(final Script script,
			final AutomataLibraryServices services, final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException {

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
	public static NestedLassoWord<MSODAlphabetSymbol> getWordBuchi(final Script script,
			final AutomataLibraryServices services, final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataLibraryException {

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
	public static Pair<NestedWord<MSODAlphabetSymbol>, NestedWord<MSODAlphabetSymbol>>
			splitWordWeak(final Script script, final NestedWord<MSODAlphabetSymbol> word) {
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
	public static Pair<NestedLassoWord<MSODAlphabetSymbol>, NestedLassoWord<MSODAlphabetSymbol>>
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
	public static Map<Term, Set<BigInteger>> extractStemNumbers(final Script script,
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
	public static Map<Term, Term> constructStemTerm(final Script script, final Map<Term, Set<BigInteger>> stemNumbers) {
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
	public static Map<Term, Term> constructLoopTerm(final Script script, final NestedWord<MSODAlphabetSymbol> loop,
			final Set<Term> terms, final int stemNumber) {
		final Map<Term, Term> result = new HashMap<>();
		final BigInteger loopLength = BigInteger.valueOf(loop.length());

		for (final Term term : terms) {
			// No IntSort variable should have indices enabled in its loop.
			// if (SmtSortUtils.isIntSort(term.getSort())) {
			// throw new InternalError("Integer representation is corrupted.");
			// }

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
			pair = new Pair<>(word, new NestedWord<>());
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
			pair = new Pair<>(word, new NestedLassoWord<>(new NestedWord<>(), new NestedWord<>()));
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