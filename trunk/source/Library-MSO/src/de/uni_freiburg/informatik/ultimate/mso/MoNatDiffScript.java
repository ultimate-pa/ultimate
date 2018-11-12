/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Determinize;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;

/**
 * @Questions How to use SmtUtils.toCNF()? (Might be helpful for dealing with
 *            disjunction, implication, equality)
 * 
 *            One-transitions in {@link #processExists} are not needed?.
 * 
 *            Why is {@link SmtUtils#geq} not usable in {@link #processEqual},
 *            {@link #processGreater}?
 * 
 *            Model is sometimes not minimal?
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MoNatDiffScript extends NoopScript {

	private final IUltimateServiceProvider mUSP;
	private final AutomataLibraryServices mALS;
	public final ILogger mLogger;
	private Term mAssertionTerm;

	public MoNatDiffScript(final IUltimateServiceProvider services, final ILogger logger) {
		mUSP = services;
		mALS = new AutomataLibraryServices(services);
		mLogger = logger;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mAssertionTerm = mAssertionTerm == null ? term : term("and", new Term[] { mAssertionTerm, term });
		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nwa = traversePostOrder(mAssertionTerm);
		checkEmptiness(nwa);

		// mLogger.info("RESULT: " + nwaToString(nwa, Format.ATS));

		return null;
	}

	/**
	 * Traverses formula in post order.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> traversePostOrder(final Term term) {
		mLogger.info("Traverse term: " + term);

		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;

			if (quantifiedFormula.getQuantifier() == QuantifiedFormula.FORALL)
				return processForall(quantifiedFormula);

			if (quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS)
				return processExists(quantifiedFormula);
		}

		if (term instanceof ApplicationTerm) {
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			final String functionSymbol = applicationTerm.getFunction().getName();

			if (functionSymbol.equals("true"))
				return processTrue();

			if (functionSymbol.equals("false"))
				return processFalse();

			if (functionSymbol.equals("not"))
				return processNegation(applicationTerm);

			if (functionSymbol.equals("and"))
				return processConjunction(applicationTerm);

			if (functionSymbol.equals("or"))
				return processDisjunction(applicationTerm);

			if (functionSymbol.equals("=>"))
				return processImplication(applicationTerm);

			if (functionSymbol.equals("strictSubsetInt"))
				return processStrictSubset(applicationTerm);

			if (functionSymbol.equals("subsetInt"))
				return processSubset(applicationTerm);

			if (functionSymbol.equals("element"))
				return processElement(applicationTerm);

			if (functionSymbol.equals("="))
				return processEqual(applicationTerm);

			if (functionSymbol.equals(">"))
				return processGreater(applicationTerm);

			if (functionSymbol.equals(">="))
				return processGreaterEqual(applicationTerm);

			if (functionSymbol.equals("<") || functionSymbol.equals("<="))
				return processLessOrLessEqual(applicationTerm);
		}

		throw new IllegalArgumentException("Input must be a QuantifiedFormula or an ApplicationTerm.");
	}

	/**
	 * Performs equivalent transformation from universal to existential quantifier.
	 * Calls {@link #traversePostOrder(Term)} with the result".
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processForall(final QuantifiedFormula term) {
		final Term subformula = SmtUtils.not(this, term.getSubformula());
		final Term exists = SmtUtils.not(this, quantifier(QuantifiedFormula.EXISTS, term.getVariables(), subformula));

		return traversePostOrder(exists);
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processExists(final QuantifiedFormula term) {
		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result = traversePostOrder(term.getSubformula());
		mLogger.info("Construct ∃ φ: " + term);

		Set<MoNatDiffAlphabetSymbol> zeros, ones;
		final Term[] quantifiedVariables = term.getVariables();
		zeros = MoNatDiffUtils.allMatchesAlphabet(result.getAlphabet(), false, quantifiedVariables);
		ones = MoNatDiffUtils.allMatchesAlphabet(result.getAlphabet(), true, quantifiedVariables);

		final Set<String> additionalFinals = new HashSet<String>();
		final Queue<String> states = new LinkedList<String>(result.getFinalStates());

		while (!states.isEmpty()) {
			final Set<String> preds = MoNatDiffUtils.hierarchicalPredecessorsIncoming(result, states.poll(), zeros);

			for (final String pred : preds) {
				if (!result.isFinal(pred) && additionalFinals.add(pred))
					states.add(pred);
			}
		}

		final Set<Term> freeVars = new HashSet<Term>(result.getAlphabet().iterator().next().getMap().keySet());
		freeVars.removeAll(Arrays.asList(quantifiedVariables));

		Set<MoNatDiffAlphabetSymbol> reducedAlphabet;
		reducedAlphabet = MoNatDiffUtils.createAlphabet(freeVars.toArray(new Term[0]));
		result = MoNatDiffAutomatonFactory.reconstruct(mALS, result, reducedAlphabet, false);
		result = makeStatesFinal(result, additionalFinals);

		return result;
	}

	/**
	 * Returns automaton that represents "true".
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processTrue() {
		mLogger.info("Construct true");

		return MoNatDiffAutomatonFactory.trueAutomaton(mALS);
	}

	/**
	 * Returns automaton that represents "false".
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processFalse() {
		mLogger.info("Construct false");

		return MoNatDiffAutomatonFactory.falseAutomaton(mALS);
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processNegation(final ApplicationTerm term) {
		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct not φ: " + term);

		result = complement(result);

		if (result.getAlphabet().isEmpty())
			return result;

		final Set<Term> intVars = new HashSet<Term>(result.getAlphabet().iterator().next().getMap().keySet());
		intVars.removeIf(o -> !MoNatDiffUtils.isIntVariable(o));

		for (final Term intVar : intVars) {
			NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> varAutomaton;
			varAutomaton = MoNatDiffAutomatonFactory.intVariableAutomaton(mALS, intVar);
			varAutomaton = MoNatDiffAutomatonFactory.reconstruct(mALS, varAutomaton, result.getAlphabet(), true);
			result = intersect(result, varAutomaton);
		}

		return result;
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processConjunction(final ApplicationTerm term) {
		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct φ and ψ (0): " + term);

		for (int i = 1; i < term.getParameters().length; i++) {
			INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> tmp = traversePostOrder(term.getParameters()[i]);
			mLogger.info("Construct φ and ψ (" + i + "): " + term);

			Set<MoNatDiffAlphabetSymbol> symbols;
			symbols = MoNatDiffUtils.mergeAlphabets(result.getAlphabet(), tmp.getAlphabet());

			result = MoNatDiffAutomatonFactory.reconstruct(mALS, result, symbols, true);
			tmp = MoNatDiffAutomatonFactory.reconstruct(mALS, tmp, symbols, true);
			result = intersect(result, tmp);
		}

		return result;
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processDisjunction(final ApplicationTerm term) {
		final Term[] terms = new Term[term.getParameters().length];

		for (int i = 0; i < term.getParameters().length; i++)
			terms[i] = SmtUtils.not(this, term.getParameters()[i]);

		final Term conjunction = SmtUtils.not(this, SmtUtils.and(this, terms));

		return traversePostOrder(conjunction);
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processImplication(final ApplicationTerm term) {
		final Term[] terms = term.getParameters();

		for (int i = 0; i < terms.length - 1; i++)
			terms[i] = SmtUtils.not(this, terms[i]);

		return traversePostOrder(SmtUtils.or(this, terms));
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processEqual(final ApplicationTerm term) {
		final Term[] terms = term.getParameters();
		final Term lessEqual = SmtUtils.leq(this, terms[0], terms[1]);
		final Term greaterEqual = SmtUtils.not(this, SmtUtils.less(this, terms[0], terms[1]));
		final Term equal = SmtUtils.and(this, lessEqual, greaterEqual);

		return traversePostOrder(equal);
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processGreater(final ApplicationTerm term) {
		final Term[] terms = term.getParameters();
		final Term greater = SmtUtils.not(this, SmtUtils.leq(this, terms[0], terms[1]));

		return traversePostOrder(greater);
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processGreaterEqual(final ApplicationTerm term) {
		final Term[] terms = term.getParameters();
		final Term greaterEqual = SmtUtils.not(this, SmtUtils.less(this, terms[0], terms[1]));

		return traversePostOrder(greaterEqual);
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processLessOrLessEqual(final ApplicationTerm term) {
		final AffineRelation affineRelation = affineRelation(term, TransformInequality.NONSTRICT2STRICT);
		final AffineTerm affineTerm = affineRelation.getAffineTerm();
		final Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		final Rational constant = affineTerm.getConstant().negate();

		if (variables.size() == 1) {
			final Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (var.getValue().equals(Rational.ONE)) {
				mLogger.info("Construct x < c: " + term);
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(mALS, var.getKey(), constant);
			}

			if (var.getValue().equals(Rational.MONE)) {
				mLogger.info("Construct -x < c: " + term);
				return MoNatDiffAutomatonFactory.strictNegIneqAutomaton(mALS, var.getKey(), constant);
			}
		}

		if (variables.size() == 2) {
			mLogger.info("Construct x-y < c: " + affineTerm);

			final Iterator<Entry<Term, Rational>> it = variables.entrySet().iterator();
			final Entry<Term, Rational> var1 = it.next();
			final Entry<Term, Rational> var2 = it.next();

			mLogger.info(var1 + " - " + var2 + " < " + constant);

			if (!var1.getValue().add(var2.getValue()).equals(Rational.ZERO))
				throw new IllegalArgumentException("Input is not difference logic.");

			if (var1.getValue().equals(Rational.ONE))
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(mALS, var1.getKey(), var2.getKey(), constant);

			if (var2.getValue().equals(Rational.ONE))
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(mALS, var2.getKey(), var1.getKey(), constant);
		}

		throw new IllegalArgumentException("Invalid inequality");
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processStrictSubset(final ApplicationTerm term) {
		mLogger.info("Construct X strictSubset Y: " + term);

		if (term.getParameters().length != 2)
			throw new IllegalArgumentException("StrictSubset must have exactly two parameters.");

		return MoNatDiffAutomatonFactory.strictSubsetAutomaton(mALS, term.getParameters()[0], term.getParameters()[1]);
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processSubset(final ApplicationTerm term) {
		mLogger.info("Construct X subset Y: " + term);

		if (term.getParameters().length != 2)
			throw new IllegalArgumentException("Subset must have exactly two parameters.");

		return MoNatDiffAutomatonFactory.subsetAutomaton(mALS, term.getParameters()[0], term.getParameters()[1]);
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processElement(final ApplicationTerm term) {
		if (term.getParameters().length != 2)
			throw new IllegalArgumentException("Element must have exactly two parameters.");

		final AffineTerm affineTerm = affineTerm(term.getParameters()[0]);
		final Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		final Rational constant = affineTerm.getConstant();

		if (variables.size() == 0) {
			mLogger.info("Construct c element X: " + term);
			return MoNatDiffAutomatonFactory.constElementAutomaton(mALS, constant, term.getParameters()[1]);
		}

		if (variables.size() == 1) {
			mLogger.info("Construct x+c element Y: " + term);
			final Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (!var.getValue().equals(Rational.ONE))
				throw new IllegalArgumentException("Invalid input.");

			return MoNatDiffAutomatonFactory.elementAutomaton(mALS, var.getKey(), constant, term.getParameters()[1]);
		}

		throw new IllegalArgumentException("Invalid input.");
	}

	/*
	 * Returns a automaton where also the given states are final.
	 * 
	 * @throws IllegalArgumentException if operation fails.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> makeStatesFinal(
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nwa, final Set<String> states) {

		NestedWordAutomatonReachableStates<MoNatDiffAlphabetSymbol, String> nwaReachableStates;

		try {
			nwaReachableStates = new NestedWordAutomatonReachableStates<>(mALS, nwa);
		} catch (final AutomataOperationCanceledException e) {
			throw new IllegalArgumentException("Could not create NestedWordAutomatonReachableStates: " + e);
		}

		final Set<String> finals = new HashSet<String>(nwa.getFinalStates());
		finals.addAll(states);

		return new NestedWordAutomatonFilteredStates<MoNatDiffAlphabetSymbol, String>(mALS, nwaReachableStates,
				nwa.getStates(), nwa.getInitialStates(), finals);
	}

	/**
	 * Checks if the language of the given automaton is empty.
	 * 
	 * @throws IllegalArgumentException
	 *             if operation fails.
	 */
	private void checkEmptiness(final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nwa) {
		IsEmpty<MoNatDiffAlphabetSymbol, String> isEmpty;

		try {
			isEmpty = new IsEmpty<MoNatDiffAlphabetSymbol, String>(mALS, nwa);
		} catch (final AutomataOperationCanceledException e) {
			throw new IllegalArgumentException("Could not create IsEmpty: " + e);
		}

		if (isEmpty.getResult()) {
			mLogger.info("RESULT: UNSAT");
			return;
		}

		final NestedRun<MoNatDiffAlphabetSymbol, String> run = isEmpty.getNestedRun();
		final NestedWord<MoNatDiffAlphabetSymbol> word = run.getWord();

		mLogger.info("RESULT: SAT");
		mLogger.info("MODEL: " + MoNatDiffUtils.wordMoNatDiffToInteger(word));
	}

	/**
	 * Helper function. Returns {@link AffineTerm} that corresponds to the given
	 * term.
	 * 
	 * @throws IllegalArgumentException
	 *             if operation fails.
	 */
	private AffineTerm affineTerm(final Term term) {
		final AffineTerm affineTerm = (AffineTerm) new AffineTermTransformer(this).transform(term);

		if (affineTerm.isErrorTerm())
			throw new IllegalArgumentException("Could not create AffineTerm.");

		return affineTerm;
	}

	/**
	 * Helper function. Returns {@link AffineRelation} that corresponds to the given
	 * term.
	 * 
	 * @throws IllegalArgumentException
	 *             if operation fails.
	 */
	private AffineRelation affineRelation(final Term term, final TransformInequality transformInequality) {
		AffineRelation affineRelation;

		try {
			affineRelation = new AffineRelation(this, term, transformInequality);
		} catch (final NotAffineException e) {
			throw new IllegalArgumentException("Could not create AffineRelation: " + e);
		}

		return affineRelation;
	}

	/**
	 * Helper function. Returns {@link Complement} of the given automaton.
	 * 
	 * @throws IllegalArgumentException
	 *             if operation fails.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> complement(
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton) {

		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> complement;

		try {
			complement = new Complement<>(mALS, new StringFactory(), automaton).getResult();
		} catch (final AutomataOperationCanceledException e) {
			throw new IllegalArgumentException("Could not create Complement: " + e);
		}

		return complement;
	}

	/**
	 * Helper function. Returns {@link Intersection} of the given automata.
	 * 
	 * @throws IllegalArgumentException
	 *             if operation fails.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> intersect(
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton2) {

		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> intersection;

		try {
			intersection = new Intersect<>(mALS, new StringFactory(), automaton1, automaton2).getResult();
		} catch (final AutomataLibraryException e) {
			throw new IllegalArgumentException("Could not create Intersection: " + e);
		}

		return intersection;
	}

	/*
	 * Returns a collection as String. Only used for debugging.
	 */
	private String collectionToString(final Iterable<?> iterable) {
		return StreamSupport.stream(iterable.spliterator(), false).map(o -> o.toString())
				.collect(Collectors.joining(" | "));
	}

	/*
	 * Returns a NestedWordAutomaton as String. Only used for debugging.
	 */
	private String nwaToString(final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nwa, final Format format) {
		return new AutomatonDefinitionPrinter(mALS, "", Format.ATS, nwa).getDefinitionAsString();
	}

	/*
	 * Examples. TODO: Remove later.
	 */
	private void constructAutomaton() throws AutomataLibraryException {
		final Set<Integer> alphabet = null;
		final VpAlphabet<Integer> vpAlphabet = new VpAlphabet<Integer>(alphabet);
		final StringFactory stateFactory = new StringFactory();
		final NestedWordAutomaton<Integer, String> automaton = new NestedWordAutomaton<Integer, String>(mALS,
				vpAlphabet, stateFactory);

		// add some initial state
		automaton.addState(true, false, "q_0");
		// add some accepting state
		automaton.addState(false, true, "q_1");
		// connect both states via transition that is labeled by letter 23
		automaton.addInternalTransition("q_0", 23, "q_1");

		final INestedWordAutomaton<Integer, String> intersection = new Intersect<Integer, String>(mALS, stateFactory,
				automaton, automaton).getResult();
		final INestedWordAutomaton<Integer, String> buchiIntersection = new BuchiIntersect<Integer, String>(mALS,
				stateFactory, automaton, automaton).getResult();
		final INestedWordAutomaton<Integer, String> union = new Union<Integer, String>(mALS, stateFactory, automaton,
				automaton).getResult();
		final INestedWordAutomaton<Integer, String> determinize = new Determinize<Integer, String>(mALS, stateFactory,
				automaton).getResult();
		final INestedWordAutomaton<Integer, String> complement = new Complement<Integer, String>(mALS, stateFactory,
				automaton).getResult();
		final INestedWordAutomaton<Integer, String> buchiComplement = new BuchiComplementFKV<Integer, String>(mALS,
				stateFactory, automaton).getResult();

		final IsEmpty<Integer, String> emptinessCheck = new IsEmpty<Integer, String>(mALS, union);
		if (emptinessCheck.getResult() == false) {
			final NestedRun<Integer, String> run = emptinessCheck.getNestedRun();
			final NestedWord<Integer> word = run.getWord();
		}

		final BuchiIsEmpty<Integer, String> buchiEmptinessCheck = new BuchiIsEmpty<Integer, String>(mALS,
				buchiComplement);
		if (emptinessCheck.getResult() == false) {
			final NestedLassoRun<Integer, String> lassorun = buchiEmptinessCheck.getAcceptingNestedLassoRun();
			final NestedLassoWord<Integer> lassoword = lassorun.getNestedLassoWord();
		}
	}

	/*
	 * Examples. TODO: Remove later.
	 */
	private void someAuxiliaryMethodsThatMightBeHelpfulForWorkingWithFormulas() {
		final Term term = null;
		final Term term2 = null;
		SmtUtils.isAtomicFormula(term);
		SmtUtils.and(this, term, term2);
		final QuantifiedFormula qf = (QuantifiedFormula) term;
		SmtUtils.quantifier(this, QuantifiedFormula.EXISTS, new HashSet<TermVariable>(Arrays.asList(qf.getFreeVars())),
				term);
		SmtUtils.not(this, term2);
		final ApplicationTerm appTerm = (ApplicationTerm) term2;

		if (appTerm.getFunction().getName().equals("and")) {
			// this is an and term
		}

		// data structure that might help you for working with atoms
		AffineRelation ar;
		try {
			ar = new AffineRelation(this, appTerm);
		} catch (final NotAffineException e) {
			// not an affine relation, maybe we have to descend one level in the tree!?!
			ar = null;
		}
		final AffineTerm at = ar.getAffineTerm();
		final Map<Term, Rational> var2coeff = at.getVariable2Coefficient();
		if (var2coeff.size() > 2) {
			throw new IllegalArgumentException("more than two variables! this is not difference logic");
		}
		final Rational literal = at.getConstant();
		if (!literal.isIntegral()) {
			throw new IllegalArgumentException("not a integer");
		}
		final BigInteger integer = literal.numerator();

		// TODO: another suggestion for symbols of an alphabet
		final Map<Term, Boolean> myAlphabetSymbol = new HashMap();
		myAlphabetSymbol.put(this.variable("myVariable", this.sort("Int")), true);
	}
}
