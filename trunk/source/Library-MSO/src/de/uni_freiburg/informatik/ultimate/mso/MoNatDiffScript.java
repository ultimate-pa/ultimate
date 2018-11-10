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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;

/*
 * Questions:
 * TODO: implement automaton for true, false and use them in traverse Post order
 * 1) (solved) How to deal with constant values larger than max integer in constantTermToInt()?
 * 2) How to deal with empty symbol in MoNatDiffAlphabetSymbol?
 * 3) What to do iff all variables are quantified ones? 
 * 		-> if at least one accepting state is reachable -> true-automaton
 * 4) How to handle empty alphabets in createAlphabet?
 * 5) How to deal with accepting states before projection if no free variables exist?
 * 		-> see 3)
 * 6) Does this exist somewhere hierarchicalSuccessorsOutgoing? Is our implementation inefficient?
 * 7) (solved) How to insert final keyword with script?
 * 8) How to use SmtUtils.toCNF()? (Might be helpful for dealing with disjunction, implication, equality)
 */
public class MoNatDiffScript extends NoopScript {

	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataLibraryServies;
	public final ILogger mLogger;
	private Term mAssertionTerm;

	public MoNatDiffScript(final IUltimateServiceProvider services, final ILogger logger) {
		mServices = services;
		mAutomataLibraryServies = new AutomataLibraryServices(services);
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
		mLogger.info("Term: " + term);
		mAssertionTerm = mAssertionTerm == null ? term : term("and", new Term[] { mAssertionTerm, term });
		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nwa = traversePostOrder(mAssertionTerm);
		checkEmptiness(nwa);

		//mLogger.info("RESULT: " + nwaToString(nwa, Format.ATS));

		return null;
	}

	/*
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
			
			if (functionSymbol.equals(">"))
				return processGreater(applicationTerm);
			
			if (functionSymbol.equals(">="))
				return processGreaterEqual(applicationTerm);

			if (functionSymbol.equals("<") || functionSymbol.equals("<="))
				return processLessOrLessEqual(applicationTerm);
		}

		throw new IllegalArgumentException("Input must be a QuantifiedFormula or an ApplicationTerm. " + term);
	}

	/*
	 * TODO: Comment.
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
		mLogger.info("Construct exists Phi: " + term);

		final Set<MoNatDiffAlphabetSymbol> alphabet = result.getAlphabet();
		final Term[] quantifiedVariables = term.getVariables();

		mLogger.info("Quantified variables: " + collectionToString(Arrays.asList(quantifiedVariables)));

		final Set<MoNatDiffAlphabetSymbol> zeros = MoNatDiffUtils.allMatchesAlphabet(alphabet, false,
				quantifiedVariables);
		final Set<MoNatDiffAlphabetSymbol> ones = MoNatDiffUtils.allMatchesAlphabet(alphabet, true,
				quantifiedVariables);

		mLogger.info("0-symbols: " + collectionToString(zeros));
		mLogger.info("1-symbols: " + collectionToString(ones));

		final Set<String> additionalFinals = new HashSet<String>();
		final Queue<String> queue = new LinkedList<String>(result.getFinalStates());

		while (!queue.isEmpty()) {
			final String state = queue.poll();

			final Set<String> finals = MoNatDiffUtils.hierarchicalPredecessorsIncoming(result, state,
					zeros.toArray(new MoNatDiffAlphabetSymbol[zeros.size()]));

			for (final String f : finals) {
				if (result.isFinal(f))
					continue;

				if (additionalFinals.add(f))
					queue.add(f);
			}
		}

		// final Set<String> additionalFinals = new HashSet<String>(); Iterator<String>
		// it = result.getInitialStates().iterator(); while (it.hasNext())
		// additionalFinals.addAll(MoNatDiffUtils.hierarchicalSuccessorsOutgoing(result,
		// it.next(), ones.toArray(new MoNatDiffAlphabetSymbol[ones.size()])));
		//
		// it = result.getFinalStates().iterator(); while (it.hasNext())
		// additionalFinals.retainAll(MoNatDiffUtils.hierarchicalPredecessorsIncoming(
		// result, it.next(), zeros.toArray(new
		// MoNatDiffAlphabetSymbol[zeros.size()])));

		mLogger.info("Additional final states: " + collectionToString(additionalFinals));

		// TODO: Think about ... it changes the alphabet of the given nwa.
		final Set<Term> terms = alphabet.iterator().next().getMap().keySet();
		terms.removeAll(Arrays.asList(quantifiedVariables));
		final Set<MoNatDiffAlphabetSymbol> reducedAlphabet = MoNatDiffUtils
				.createAlphabet(terms.toArray(new Term[terms.size()]));

		mLogger.info("Reduced alphabet: " + collectionToString(reducedAlphabet));

		result = MoNatDiffAutomatonFactory.reconstruct(mAutomataLibraryServies, result, reducedAlphabet, false, mLogger);

		result = makeStatesFinal(result, additionalFinals);
		// mLogger.info("EXISTS: " + nwaToString(result, Format.ATS));

		return result;
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processNegation(final ApplicationTerm term) {

		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result = traversePostOrder(term.getParameters()[0]);
		mLogger.info("Construct not Phi: " + term);

		try {
			result = new Complement<>(mAutomataLibraryServies, new StringFactory(), result).getResult();
		} catch (final AutomataOperationCanceledException e) {
			mLogger.info("ERROR: " + e);
		}
		
		final Set<Term> terms = new HashSet<Term>(result.getAlphabet().iterator().next().getMap().keySet());

		mLogger.info("Variables: " + collectionToString(terms));
		terms.removeIf(o -> !MoNatDiffUtils.isIntVariable(o));
		mLogger.info("IntVariables: " + collectionToString(terms));		

		final Iterator<Term> itTerms = terms.iterator();
		while (itTerms.hasNext()) {
			NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> variableAutomaton = MoNatDiffAutomatonFactory
					.intVariableAutomaton(mAutomataLibraryServies, itTerms.next());

			variableAutomaton = MoNatDiffAutomatonFactory.reconstruct(mAutomataLibraryServies, variableAutomaton,
					result.getAlphabet(), true, mLogger);

			try {
				result = new Intersect<>(mAutomataLibraryServies, new StringFactory(), result, variableAutomaton)
						.getResult();
			} catch (final AutomataLibraryException e) {
				mLogger.info("ERROR: " + e);
			}
		}

		return result;
	}

	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processConjunction(final ApplicationTerm term) {

		final Term[] terms = term.getParameters();
		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result = traversePostOrder(terms[0]);
		mLogger.info("Construct Phi and Psi (0): " + term);

		for (int i = 1; i < terms.length; i++) {
			INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = traversePostOrder(terms[i]);
			mLogger.info("Construct Phi and Psi (" + i + "): " + term);

			final Set<MoNatDiffAlphabetSymbol> alphabet = MoNatDiffUtils.mergeAlphabets(result.getAlphabet(),
					automaton.getAlphabet());

			result = MoNatDiffAutomatonFactory.reconstruct(mAutomataLibraryServies, result, alphabet, true, mLogger);
			automaton = MoNatDiffAutomatonFactory.reconstruct(mAutomataLibraryServies, automaton, alphabet, true, mLogger);

			try {
				result = new Intersect<>(mAutomataLibraryServies, new StringFactory(), result, automaton).getResult();
			} catch (final AutomataLibraryException e) {
				mLogger.info("ERROR: " + e);
			}
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
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processGreater(final ApplicationTerm term) {
		final Term[] terms = term.getParameters();	
		final Term lessEqual = SmtUtils.not(this, SmtUtils.leq(this, terms[0], terms[1]));

		return traversePostOrder(lessEqual);
	}
	
	/*
	 * TODO: Comment.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processGreaterEqual(final ApplicationTerm term) {
		final Term[] terms = term.getParameters();	
		final Term less = SmtUtils.not(this, SmtUtils.less(this, terms[0], terms[1]));

		return traversePostOrder(less);
	}
	
	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processLessOrLessEqual(final ApplicationTerm term) {
		final AffineRelation affineRelation = MoNatDiffUtils.makeAffineRelation(this, term,
				TransformInequality.NONSTRICT2STRICT);
		final AffineTerm affineTerm = affineRelation.getAffineTerm();
		final Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		final Rational constant = affineTerm.getConstant().negate();

		if (variables.size() == 1) {
			final Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (var.getValue().equals(Rational.ONE)) {
				mLogger.info("Construct x < c: " + term);
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(mAutomataLibraryServies, var.getKey(), constant);
			}

			if (var.getValue().equals(Rational.MONE)) {
				mLogger.info("Construct -x < c: " + term);
				return MoNatDiffAutomatonFactory.strictNegIneqAutomaton(mAutomataLibraryServies, var.getKey(),
						constant);
			}
		}

		if (variables.size() == 2) {
			mLogger.info("Construct x-y < c: " + term);

			final Iterator<Entry<Term, Rational>> it = variables.entrySet().iterator();
			final Entry<Term, Rational> var1 = it.next();
			final Entry<Term, Rational> var2 = it.next();
			
			mLogger.info(var1 + " - " + var2 + " < " + constant);

			if (!var1.getValue().add(var2.getValue()).equals(Rational.ZERO))
				throw new IllegalArgumentException("Input is not difference logic.");

			if (var1.getValue().equals(Rational.ONE))
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(mAutomataLibraryServies, var1.getKey(),
						var2.getKey(), constant);

			if (var2.getValue().equals(Rational.ONE))
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(mAutomataLibraryServies, var2.getKey(),
						var1.getKey(), constant);
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

		return MoNatDiffAutomatonFactory.strictSubsetAutomaton(mAutomataLibraryServies, term.getParameters()[0],
				term.getParameters()[1]);
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processSubset(final ApplicationTerm term) {
		mLogger.info("Construct X subset Y: " + term);

		if (term.getParameters().length != 2)
			throw new IllegalArgumentException("Subset must have exactly two parameters.");

		return MoNatDiffAutomatonFactory.subsetAutomaton(mAutomataLibraryServies, term.getParameters()[0],
				term.getParameters()[1]);
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processElement(final ApplicationTerm term) {
		if (term.getParameters().length != 2)
			throw new IllegalArgumentException("Element must have exactly two parameters.");
		
		final AffineTerm affineTerm = MoNatDiffUtils.makeAffineTerm(this, term.getParameters()[0], mLogger);
		final Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		final Rational constant = affineTerm.getConstant();

		if (variables.size() == 0) {
			mLogger.info("Construct c element X: " + term);
			return MoNatDiffAutomatonFactory.constElementAutomaton(mAutomataLibraryServies, constant,
					term.getParameters()[1]);
		}

		if (variables.size() == 1) {
			mLogger.info("Construct x+c element Y: " + term);
			final Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (!var.getValue().equals(Rational.ONE))
				throw new IllegalArgumentException("Invalid input.");
			
			return MoNatDiffAutomatonFactory.elementAutomaton(mAutomataLibraryServies, var.getKey(), constant,
					term.getParameters()[1]);
		}

		throw new IllegalArgumentException("Invalid input.");
	}

	/*
	 * Makes states final in the given NestedWordAutomaton.
	 */
	private INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> makeStatesFinal(
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nwa, final Set<String> finals) {

		NestedWordAutomatonReachableStates<MoNatDiffAlphabetSymbol, String> nwaReachableStates = null;

		try {
			nwaReachableStates = new NestedWordAutomatonReachableStates<>(mAutomataLibraryServies, nwa);
		} catch (final AutomataOperationCanceledException e) {
			mLogger.info("ERROR: " + e);
		}

		final Set<String> newFinals = new HashSet<String>(nwa.getFinalStates());
		newFinals.addAll(finals);

		// NullPointerException if nwaReachableStates == null.
		return new NestedWordAutomatonFilteredStates<MoNatDiffAlphabetSymbol, String>(mAutomataLibraryServies,
				nwaReachableStates, nwa.getStates(), nwa.getInitialStates(), newFinals);
	}

	/*
	 * Checks if the language of the given NestedWordAutomaton is empty.
	 */
	private void checkEmptiness(final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nwa) {
		IsEmpty<MoNatDiffAlphabetSymbol, String> isEmpty = null;

		try {
			isEmpty = new IsEmpty<MoNatDiffAlphabetSymbol, String>(mAutomataLibraryServies, nwa);
		} catch (final AutomataOperationCanceledException e) {
			mLogger.info("ERROR: " + e);
		}
		
		if (isEmpty.getResult())
		{
			mLogger.info("Language is empty.");
			return;
		}

		final NestedRun<MoNatDiffAlphabetSymbol, String> run = isEmpty.getNestedRun();
		final NestedWord<MoNatDiffAlphabetSymbol> word = run.getWord();
		
		mLogger.info("Accepting word: \"" + word + "\"");
		
		if (word.length() == 0)
			return;
			
		final Set<Term> terms = word.getSymbol(0).getMap().keySet();
		final Map<Term, List<Integer>> result = new HashMap<Term, List<Integer>>();
		
		for (int i = 0; i < word.length(); i++)
		{
			final MoNatDiffAlphabetSymbol symbol = word.getSymbol(i);
			
			for (final Term term : terms)
			{
				if (!result.containsKey(term))
					result.put(term, new ArrayList<Integer>());
				
				if (symbol.getMap().get(term))
					result.get(term).add(i);
			}
		}
		
		
		mLogger.info("Model: " + result);
		
		return;

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
		return new AutomatonDefinitionPrinter(mAutomataLibraryServies, "", Format.ATS, nwa).getDefinitionAsString();
	}

	/*
	 * Examples. TODO: Remove later.
	 */
	private void constructAutomaton() throws AutomataLibraryException {
		final Set<Integer> alphabet = null;
		final VpAlphabet<Integer> vpAlphabet = new VpAlphabet<Integer>(alphabet);
		final StringFactory stateFactory = new StringFactory();
		final NestedWordAutomaton<Integer, String> automaton = new NestedWordAutomaton<Integer, String>(
				mAutomataLibraryServies, vpAlphabet, stateFactory);

		// add some initial state
		automaton.addState(true, false, "q_0");
		// add some accepting state
		automaton.addState(false, true, "q_1");
		// connect both states via transition that is labeled by letter 23
		automaton.addInternalTransition("q_0", 23, "q_1");

		final INestedWordAutomaton<Integer, String> intersection = new Intersect<Integer, String>(
				mAutomataLibraryServies, stateFactory, automaton, automaton).getResult();
		final INestedWordAutomaton<Integer, String> buchiIntersection = new BuchiIntersect<Integer, String>(
				mAutomataLibraryServies, stateFactory, automaton, automaton).getResult();
		final INestedWordAutomaton<Integer, String> union = new Union<Integer, String>(mAutomataLibraryServies,
				stateFactory, automaton, automaton).getResult();
		final INestedWordAutomaton<Integer, String> determinize = new Determinize<Integer, String>(
				mAutomataLibraryServies, stateFactory, automaton).getResult();
		final INestedWordAutomaton<Integer, String> complement = new Complement<Integer, String>(
				mAutomataLibraryServies, stateFactory, automaton).getResult();
		final INestedWordAutomaton<Integer, String> buchiComplement = new BuchiComplementFKV<Integer, String>(
				mAutomataLibraryServies, stateFactory, automaton).getResult();

		final IsEmpty<Integer, String> emptinessCheck = new IsEmpty<Integer, String>(mAutomataLibraryServies, union);
		if (emptinessCheck.getResult() == false) {
			final NestedRun<Integer, String> run = emptinessCheck.getNestedRun();
			final NestedWord<Integer> word = run.getWord();
		}

		final BuchiIsEmpty<Integer, String> buchiEmptinessCheck = new BuchiIsEmpty<Integer, String>(
				mAutomataLibraryServies, buchiComplement);
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
