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
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
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

/*
 * Questions:
 * 1) How to deal with constant values larger than max integer in constantTermToInt()?
 * 2) How to deal with empty symbol in MoNatDiffAlphabetSymbol?
 */
public class MoNatDiffScript extends NoopScript {

	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataLibraryServices;
	private final ILogger mLogger;

	public MoNatDiffScript(final IUltimateServiceProvider services, final ILogger logger) {
		mServices = services;
		mAutomataLibraryServices = new AutomataLibraryServices(services);
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
		// TODO Auto-generated method stub

		mLogger.info("formula: " + term);
		checkEmptiness(traversePostOrder(term));

		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * Traverses formula in post order.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> traversePostOrder(Term term) {
		mLogger.info("term: " + term);

		if (term instanceof QuantifiedFormula) {
			QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;
			traversePostOrder(quantifiedFormula.getSubformula());
		}

		if (term instanceof ApplicationTerm) {
			ApplicationTerm applicationTerm = (ApplicationTerm) term;
			String functionSymbol = applicationTerm.getFunction().getName();

			if (functionSymbol.equals("not"))
				return processNot(applicationTerm);

			if (functionSymbol.equals("and"))
				return processAnd(applicationTerm);

			if (functionSymbol.equals("strictSubsetInt"))
				return processStrictSubset(applicationTerm);

			if (functionSymbol.equals("subsetInt"))
				return processSubset(applicationTerm);

			if (functionSymbol.equals("element"))
				return processElement(applicationTerm);

			if (functionSymbol.equals("<") || functionSymbol.equals("<="))
				return processInequality(applicationTerm);
		}

		throw new IllegalArgumentException("Input must be QuantifiedFormula or ApplicationTerm.");
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processNot(ApplicationTerm term) {
		mLogger.info("Construct not.");

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = traversePostOrder(term.getParameters()[0]);
		StringFactory stateFactory = new StringFactory();

		try {
			INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> complement = new Complement<MoNatDiffAlphabetSymbol, String>(
					mAutomataLibraryServices, stateFactory, automaton).getResult();

			checkEmptiness(complement);

		} catch (AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		return automaton;
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processAnd(ApplicationTerm term) {
		mLogger.info("Construct and.");

		Term[] terms = term.getParameters();
		for (int i = 0; i < terms.length; i++) {
			traversePostOrder(terms[i]);
		}

		return null;
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processInequality(ApplicationTerm term) {
		AffineRelation affineRelation;
		try {
			affineRelation = new AffineRelation(this, term, TransformInequality.NONSTRICT2STRICT);
		} catch (NotAffineException e) {
			throw new IllegalArgumentException("Not an AffineRelation.");
		}

		AffineTerm affineTerm = affineRelation.getAffineTerm();
		Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		Rational constant = affineTerm.getConstant().negate();

		if (variables.size() == 1) {
			Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (var.getValue().equals(Rational.ONE)) {
				mLogger.info("Construct x < c.");

				return MoNatDiffAutomatonFactory.strictIneqAutomaton(var.getKey(), constant, mAutomataLibraryServices);
			}

			if (var.getValue().equals(Rational.MONE)) {
				mLogger.info("Construct -x < c.");

				return MoNatDiffAutomatonFactory.strictNegIneqAutomaton(var.getKey(), constant,
						mAutomataLibraryServices);
			}
		}

		if (variables.size() == 2) {
			mLogger.info("Construct x-y < c.");

			Iterator<Entry<Term, Rational>> it = variables.entrySet().iterator();
			Entry<Term, Rational> var1 = it.next();
			Entry<Term, Rational> var2 = it.next();

			if (!var1.getValue().add(var2.getValue()).equals(Rational.ZERO))
				throw new IllegalArgumentException("Input is not difference logic.");

			if (var1.getValue().equals(Rational.ONE))
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(var1.getKey(), var2.getKey(), constant,
						mAutomataLibraryServices);

			if (var2.getValue().equals(Rational.ONE))
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(var2.getKey(), var1.getKey(), constant,
						mAutomataLibraryServices);
		}

		throw new IllegalArgumentException("Invalid inequality");
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processStrictSubset(ApplicationTerm term) {
		mLogger.info("Construct X strictSubset Y.");

		if (term.getParameters().length != 2)
			throw new IllegalArgumentException("StrictSubset must have exactly two parameters.");

		return MoNatDiffAutomatonFactory.strictSubsetAutomaton(term.getParameters()[0], term.getParameters()[1],
				mAutomataLibraryServices);
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processSubset(ApplicationTerm term) {
		mLogger.info("Construct X subset Y.");

		if (term.getParameters().length != 2)
			throw new IllegalArgumentException("Subset must have exactly two parameters.");

		return MoNatDiffAutomatonFactory.subsetAutomaton(term.getParameters()[0], term.getParameters()[1],
				mAutomataLibraryServices);
	}

	/*
	 * TODO: Comment.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> processElement(ApplicationTerm term) {
		if (term.getParameters().length != 2)
			throw new IllegalArgumentException("Element must have exactly two parameters.");

		AffineTerm affineTerm = (AffineTerm) (new AffineTermTransformer(this)).transform(term.getParameters()[0]);
		Map<Term, Rational> variables = affineTerm.getVariable2Coefficient();
		Rational constant = affineTerm.getConstant();

		if (variables.size() == 0) {
			mLogger.info("Construct c element X.");

			return MoNatDiffAutomatonFactory.constElementAutomaton(constant, term.getParameters()[1],
					mAutomataLibraryServices);
		}

		if (variables.size() == 1) {
			mLogger.info("Construct x+c element Y.");

			Entry<Term, Rational> var = variables.entrySet().iterator().next();

			if (!var.getValue().equals(Rational.ONE))
				throw new IllegalArgumentException("Invalid input.");

			return MoNatDiffAutomatonFactory.elementAutomaton(var.getKey(), constant, term.getParameters()[1],
					mAutomataLibraryServices);
		}

		throw new IllegalArgumentException("Invalid input.");
	}

	/*
	 * TODO: Comment.
	 */
	private void checkEmptiness(INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton) {
		try {
			IsEmpty<MoNatDiffAlphabetSymbol, String> emptinessCheck = new IsEmpty<MoNatDiffAlphabetSymbol, String>(
					mAutomataLibraryServices, automaton);

			if (emptinessCheck.getResult() == false) {

				NestedRun<MoNatDiffAlphabetSymbol, String> run = emptinessCheck.getNestedRun();
				NestedWord<MoNatDiffAlphabetSymbol> word = run.getWord();

				mLogger.info("Accepting word: " + word);
			} else
				mLogger.info("Automaton is empty.");
		} catch (AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/*
	 * Only for debugging.
	 */
	private void printAutomata(INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton) {
		AutomatonDefinitionPrinter printer = new AutomatonDefinitionPrinter(mAutomataLibraryServices, "debug",
				Format.GFF, automaton);

		mLogger.info(printer.getDefinitionAsString());
	}

	/*
	 * Examples. TODO: Remove later.
	 */
	private void constructAutomaton() throws AutomataLibraryException {
		final Set<Integer> alphabet = null;
		final VpAlphabet<Integer> vpAlphabet = new VpAlphabet<Integer>(alphabet);
		final StringFactory stateFactory = new StringFactory();
		final NestedWordAutomaton<Integer, String> automaton = new NestedWordAutomaton<Integer, String>(
				mAutomataLibraryServices, vpAlphabet, stateFactory);

		// add some initial state
		automaton.addState(true, false, "q_0");
		// add some accepting state
		automaton.addState(false, true, "q_1");
		// connect both states via transition that is labeled by letter 23
		automaton.addInternalTransition("q_0", 23, "q_1");

		final INestedWordAutomaton<Integer, String> intersection = new Intersect<Integer, String>(
				mAutomataLibraryServices, stateFactory, automaton, automaton).getResult();
		final INestedWordAutomaton<Integer, String> buchiIntersection = new BuchiIntersect<Integer, String>(
				mAutomataLibraryServices, stateFactory, automaton, automaton).getResult();
		final INestedWordAutomaton<Integer, String> union = new Union<Integer, String>(mAutomataLibraryServices,
				stateFactory, automaton, automaton).getResult();
		final INestedWordAutomaton<Integer, String> determinize = new Determinize<Integer, String>(
				mAutomataLibraryServices, stateFactory, automaton).getResult();
		final INestedWordAutomaton<Integer, String> complement = new Complement<Integer, String>(
				mAutomataLibraryServices, stateFactory, automaton).getResult();
		final INestedWordAutomaton<Integer, String> buchiComplement = new BuchiComplementFKV<Integer, String>(
				mAutomataLibraryServices, stateFactory, automaton).getResult();

		final IsEmpty<Integer, String> emptinessCheck = new IsEmpty<Integer, String>(mAutomataLibraryServices, union);
		if (emptinessCheck.getResult() == false) {
			final NestedRun<Integer, String> run = emptinessCheck.getNestedRun();
			final NestedWord<Integer> word = run.getWord();
		}

		final BuchiIsEmpty<Integer, String> buchiEmptinessCheck = new BuchiIsEmpty<Integer, String>(
				mAutomataLibraryServices, buchiComplement);
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
		Map<Term, Boolean> myAlphabetSymbol = new HashMap();
		myAlphabetSymbol.put(this.variable("myVariable", this.sort("Int")), true);
	}
}
