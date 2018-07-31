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
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
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
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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
		mLogger.info("hello world, logic set to " + logic);
		super.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mLogger.info("hello world, logic set to " + logic);
		super.setLogic(logic);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		
		mLogger.info("term: " + term);
		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = traversePostOrder(term);

		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}
	
	private void checkEmptiness(NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton) {
		try {
			IsEmpty<MoNatDiffAlphabetSymbol, String> emptinessCheck =
					new IsEmpty<MoNatDiffAlphabetSymbol, String>(mAutomataLibraryServices, automaton);
			
			if (emptinessCheck.getResult() == false) {
				mLogger.info("automaton is not empty");

				NestedRun<MoNatDiffAlphabetSymbol, String> run = emptinessCheck.getNestedRun();
				NestedWord<MoNatDiffAlphabetSymbol> word = run.getWord();

				mLogger.info("accepting word: " + word);
			} else
				mLogger.info("automaton is empty");
		} catch (AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/*
	 * Traverses formula in post order.
	 * Note: Currently we are working here. AffineRelation doesn't help that much. :-(
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> traversePostOrder(Term term) {
		mLogger.info("traverse term: " + term);
		
		try {
			AffineRelation affineRelation = new AffineRelation(this, term);
			mLogger.info("Term is AffineRelation.");
			return null;
			
		} catch (final NotAffineException e) {
			mLogger.info("Term is NOT an AffineRelation.");
		}
		
		List<Term> terms = new ArrayList<Term>();
		
		if (term instanceof QuantifiedFormula) {
			QuantifiedFormula quantifiedFormula = (QuantifiedFormula)term;
			terms.add(quantifiedFormula.getSubformula());
		}
		
		if (term instanceof ApplicationTerm) {
			ApplicationTerm applicationTerm = (ApplicationTerm)term;
			terms.addAll(Arrays.asList(applicationTerm.getParameters()));
		}
		
		for (Term t : terms) {
			return traversePostOrder(t);
		}
		
		return null;
		
		/*
		if (term == null)
			return null;

		String operator = new String();
		Term term1 = null, term2 = null;

		if (term instanceof QuantifiedFormula) {
			QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;
			operator = quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS ? "exists" : "forall";
			term1 = quantifiedFormula.getSubformula();
		}

		if (term instanceof ApplicationTerm) {
			ApplicationTerm applicationTerm = (ApplicationTerm) term;
			String operator_tmp = applicationTerm.getFunction().getName();

			if (operator_tmp.equals("not") || operator_tmp.equals("and") || operator_tmp.equals("or")) {
				operator = operator_tmp;
				Term[] terms = applicationTerm.getParameters();
				term1 = terms.length > 0 ? terms[0] : null;
				term2 = terms.length > 1 ? terms[1] : null;
			}
		}

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton1 = postOrder(term1);
		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton2 = postOrder(term2);

		mLogger.info("process: " + term);
		return process(term, operator, automaton1, automaton2);
		*/
	}

	/*
	 * Processes formula.
	 * TODO: Add formula x element Y.
	 */
	private NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> process(Term term, String operator,
			NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton1,
			NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton2) {
		
		if (operator.isEmpty()) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			operator = appTerm.getFunction().getName();

			if (operator.equals("subsetInt")) {
				mLogger.info("construct nonStrictSubsetAutomaton X subset Y");
				Term[] terms = appTerm.getParameters();
				return MoNatDiffAutomatonFactory.nonStrictSubsetAutomaton(terms[0], terms[1], mAutomataLibraryServices);
			}

			if (operator.equals("strictSubsetInt")) {
				mLogger.info("construct strictSubsetAutomaton X strictSubset Y");
				Term[] terms = appTerm.getParameters();
				return MoNatDiffAutomatonFactory.strictSubsetAutomaton(terms[0], terms[1], mAutomataLibraryServices);
			}

			if (operator.equals("element")) {
				Term[] terms = appTerm.getParameters();
				if (terms[0] instanceof ConstantTerm) {
					mLogger.info("construct constElementAutomaton c element X");
					return MoNatDiffAutomatonFactory.constElementAutomaton(terms[1],
							MoNatDiffUtils.constantTermToInt(terms[0]), mAutomataLibraryServices);
				}

				ApplicationTerm term0 = (ApplicationTerm) terms[0];
				Term[] terms0 = term0.getParameters();
				mLogger.info("construct elementAutomaton x+c element Y");
				return MoNatDiffAutomatonFactory.elementAutomaton(terms0[0], terms[1],
						MoNatDiffUtils.constantTermToInt(terms0[1]), mAutomataLibraryServices);
			}

			if (operator.equals("<=")) {
				Term[] terms = appTerm.getParameters();
				ApplicationTerm term0 = terms[0] instanceof ApplicationTerm ? (ApplicationTerm) terms[0] : null;

				if (term0 == null || term0.getFunction().getParameterCount() == 0) {
					mLogger.info("construct nonStrictIneqAutomaton x <= c");
					return MoNatDiffAutomatonFactory.nonStrictIneqAutomaton(terms[0],
							MoNatDiffUtils.constantTermToInt(terms[1]), mAutomataLibraryServices);
				}

				Term[] terms0 = term0.getParameters();
				if (terms0.length == 1) {
					mLogger.info("construct nonStrictNegIneqAutomaton -x <= c");
					return MoNatDiffAutomatonFactory.nonStrictNegIneqAutomaton(terms0[0],
							MoNatDiffUtils.constantTermToInt(terms[1]), mAutomataLibraryServices);
				}

				mLogger.info("construct nonStrictIneqAutomaton x-y <= c");
				return MoNatDiffAutomatonFactory.nonStrictIneqAutomaton(terms0[0], terms0[1],
						MoNatDiffUtils.constantTermToInt(terms[1]), mAutomataLibraryServices);
			}

			if (operator.equals("<")) {
				Term[] terms = appTerm.getParameters();
				ApplicationTerm term0 = terms[0] instanceof ApplicationTerm ? (ApplicationTerm) terms[0] : null;

				if (term0 == null || term0.getFunction().getParameterCount() == 0) {
					mLogger.info("construct strictIneqAutomaton x < c");
					return MoNatDiffAutomatonFactory.strictIneqAutomaton(terms[0],
							MoNatDiffUtils.constantTermToInt(terms[1]), mAutomataLibraryServices);
				}

				Term[] terms0 = term0.getParameters();
				if (terms0.length == 1) {
					mLogger.info("construct strictNegIneqAutomaton -x < c");
					return MoNatDiffAutomatonFactory.strictNegIneqAutomaton(terms0[0],
							MoNatDiffUtils.constantTermToInt(terms[1]), mAutomataLibraryServices);
				}

				mLogger.info("construct strictIneqAutomaton x-y < c");
				return MoNatDiffAutomatonFactory.strictIneqAutomaton(terms0[0], terms0[1],
						MoNatDiffUtils.constantTermToInt(terms[1]), mAutomataLibraryServices);
			}
		}

		/*
		 * TODO: Construct automata for ... not and exist
		 */

		return null;
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
