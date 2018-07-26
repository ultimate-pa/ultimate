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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.PairXY;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;

public class MoNatDiffScript extends NoopScript
{
	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataLibraryServices;
	private final ILogger mLogger;

	public MoNatDiffScript(final IUltimateServiceProvider services, final ILogger logger)
	{
		mServices = services;
		mAutomataLibraryServices = new AutomataLibraryServices(services);
		mLogger = logger;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException
	{
		mLogger.info("hello world, logic set to " + logic);
		super.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException
	{
		mLogger.info("hello world, logic set to " + logic);
		super.setLogic(logic);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException
	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException
	{
		// TODO Auto-generated method stub
		return null;
	}
	
	/*
	 * Constructs empty automaton.
	 */
	private NestedWordAutomaton<BigInteger, String> emptyAutomaton() throws AutomataLibraryException
	{
		Set<BigInteger> alphabet = null;
		VpAlphabet<BigInteger> vpAlphabet = new VpAlphabet<BigInteger>(alphabet);
		StringFactory stateFactory = new StringFactory();
		
		return new NestedWordAutomaton<BigInteger, String>(mAutomataLibraryServices, vpAlphabet, stateFactory);
	}
	
	/*
	 * Converts term of sort Int to int.
	 */
	private int termToInt(Term term) throws NumberFormatException
	{
		if (!term.getSort().getName().equals("Int"))
			throw new IllegalArgumentException("SMTLIB sort of term is not Int");
		
		return Integer.parseInt(term.toString());
	}
	
	/*
	 * Adds loops for some constant to automaton.
	 */
	private void addConstPart(NestedWordAutomaton<BigInteger, String> automaton, int constant, BigInteger initToState,
			BigInteger predStateToState, BigInteger stateToFinal)
	{
		for (int i = 0; i < constant; i++)
		{
			String state = "c" + String.valueOf(i + 1);
			automaton.addState(false, false, state);
			
			if (i == 0)
			{
				automaton.addInternalTransition("init", initToState, state);
			}
			else
			{
				String predState = "c" + String.valueOf(i);
				automaton.addInternalTransition(predState, predStateToState, state);
			}
			
			automaton.addInternalTransition(state, stateToFinal, "final");
		}
	}
	
	/*
	 * Creates automaton for atomic formula "x-y <= c".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> nonStrictIneqAutomaton(Term x, Term y, Term c)
			throws AutomataLibraryException, NumberFormatException
	{
		int cInt = termToInt(c);
		List<Term> mapping = Arrays.asList(x, y);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();	
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addState(false, false, "s1");
		
		automaton.addInternalTransition("init", BigInteger.valueOf(0), "init");
		automaton.addInternalTransition("init", BigInteger.valueOf(1), "s1");
		automaton.addInternalTransition("s1", BigInteger.valueOf(0), "s1");
		automaton.addInternalTransition("s1", BigInteger.valueOf(2), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
		automaton.addInternalTransition("init", BigInteger.valueOf(3), "final");
		
		addConstPart(automaton, cInt, BigInteger.valueOf(2), BigInteger.valueOf(0), BigInteger.valueOf(1));
		
		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}

	/*
	 * Creates automaton for atomic formula "x-y < c".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> strictIneqAutomaton(Term x, Term y, Term c)
			throws AutomataLibraryException, NumberFormatException
	{
		int cInt = termToInt(c);
		List<Term> mapping = Arrays.asList(x, y);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();	
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addState(false, false, "s1");
		
		automaton.addInternalTransition("init", BigInteger.valueOf(0), "init");
		automaton.addInternalTransition("init", BigInteger.valueOf(1), "s1");
		automaton.addInternalTransition("s1", BigInteger.valueOf(0), "s1");
		automaton.addInternalTransition("s1", BigInteger.valueOf(2), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
		
		if (cInt > 0)
			automaton.addInternalTransition("init", BigInteger.valueOf(3), "final");
		
		addConstPart(automaton, cInt - 1, BigInteger.valueOf(2), BigInteger.valueOf(0), BigInteger.valueOf(1));
		
		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}
	
	/*
	 * Creates automaton for atomic formula "x <= c".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> nonStrictIneqAutomaton(Term x, Term c)
			throws AutomataLibraryException, NumberFormatException
	{
		int cInt = termToInt(c);
		List<Term> mapping = Arrays.asList(x);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		
		automaton.addInternalTransition("init", BigInteger.valueOf(1), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
		
		addConstPart(automaton, cInt, BigInteger.valueOf(0), BigInteger.valueOf(0), BigInteger.valueOf(1));

		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}
	
	/*
	 * Creates automaton for atomic formula "x < c".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> strictIneqAutomaton(Term x, Term c)
			throws AutomataLibraryException, NumberFormatException
	{
		int cInt = termToInt(c);
		List<Term> mapping = Arrays.asList(x);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();
		
		if (cInt > 0)
		{
			automaton.addState(true, false, "init");
			automaton.addState(false, true, "final");
			
			automaton.addInternalTransition("init", BigInteger.valueOf(1), "final");
			automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
			
			addConstPart(automaton, cInt - 1, BigInteger.valueOf(0), BigInteger.valueOf(0), BigInteger.valueOf(1));
		}

		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}
	
	/*
	 * Creates automaton for atomic formula "-x <= c".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> nonStrictNegIneqAutomaton(Term x, Term c)
			throws AutomataLibraryException, NumberFormatException
	{
		int cInt = termToInt(c);
		List<Term> mapping = Arrays.asList(x);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		
		automaton.addInternalTransition("init", BigInteger.valueOf(0), "init");
		automaton.addInternalTransition("init", BigInteger.valueOf(1), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");

		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}
	
	/*
	 * Creates automaton for atomic formula "-x < c".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> strictNegIneqAutomaton(Term x, Term c)
			throws AutomataLibraryException, NumberFormatException
	{
		int cInt = termToInt(c);
		List<Term> mapping = Arrays.asList(x);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		
		automaton.addInternalTransition("init", BigInteger.valueOf(0), "init");
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
		
		if (cInt == 0)
		{
			automaton.addState(false,  false, "s1");
			automaton.addInternalTransition("init", BigInteger.valueOf(0), "s1");
			automaton.addInternalTransition("s1", BigInteger.valueOf(1), "final");
		}
		else
		{
			automaton.addInternalTransition("init", BigInteger.valueOf(1), "final");
		}

		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}
	
	/*
	 * Creates automaton for atomic formula "X is non strict subset of Y".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> nonStrictSubsetAutomaton(Term x, Term y)
			throws AutomataLibraryException
	{
		List<Term> mapping = Arrays.asList(x, y);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		
		automaton.addInternalTransition("init", BigInteger.valueOf(0), "final");
		automaton.addInternalTransition("init", BigInteger.valueOf(2), "final");
		automaton.addInternalTransition("init", BigInteger.valueOf(3), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(2), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(3), "final");

		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}
	
	/*
	 * Creates automaton for atomic formula "X is strict subset of Y".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> strictSubsetAutomaton(Term x, Term y)
			throws AutomataLibraryException
	{
		List<Term> mapping = Arrays.asList(x, y);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		
		automaton.addInternalTransition("init", BigInteger.valueOf(0), "init");
		automaton.addInternalTransition("init", BigInteger.valueOf(3), "init");
		automaton.addInternalTransition("init", BigInteger.valueOf(2), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(2), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(3), "final");

		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}
	
	/*
	 * Creates automaton for atomic formula "x+c is element of Y".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> elementAutomaton(Term x, Term c, Term y)
			throws AutomataLibraryException, NumberFormatException
	{
		int cInt = termToInt(c);
		List<Term> mapping = Arrays.asList(x, y);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();	
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		
		automaton.addInternalTransition("init", BigInteger.valueOf(0), "init");
		automaton.addInternalTransition("init", BigInteger.valueOf(2), "init");
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(2), "final");
		
		if (cInt == 0)
		{
			automaton.addInternalTransition("init", BigInteger.valueOf(3), "final");
		}

		for (int i = 0; i < cInt; i++)
		{
			String state = "c" + String.valueOf(i + 1);
			automaton.addState(false, false, state);
			
			if (i == 0)
			{
				automaton.addInternalTransition("init", BigInteger.valueOf(1), state);
				automaton.addInternalTransition("init", BigInteger.valueOf(3), state);
			}
			
			if (i > 1)
			{
				String predState = "c" + String.valueOf(i);
				automaton.addInternalTransition(predState, BigInteger.valueOf(0), state);
				automaton.addInternalTransition(predState, BigInteger.valueOf(2), state);
			}
			
			if (i == cInt - 1)
			{
				automaton.addInternalTransition(state, BigInteger.valueOf(2), "final");
			}
		}
		
		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}
	
	/*
	 * Creates automaton for atomic formula "c is element of X".
	 */
	private PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>> constElementAutomaton(Term c, Term x)
			throws AutomataLibraryException, NumberFormatException
	{
		int cInt = termToInt(c);
		List<Term> mapping = Arrays.asList(x);
		NestedWordAutomaton<BigInteger, String> automaton = emptyAutomaton();	
		
		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		
		automaton.addInternalTransition("final", BigInteger.valueOf(0), "final");
		automaton.addInternalTransition("final", BigInteger.valueOf(1), "final");
		
		if (cInt == 0)
		{
			automaton.addInternalTransition("init", BigInteger.valueOf(1), "final");
		}

		for (int i = 0; i < cInt; i++)
		{
			String state = "c" + String.valueOf(i + 1);
			automaton.addState(false, false, state);
			
			String predState = i > 0 ? "c" + String.valueOf(i) : "init";
			automaton.addInternalTransition(predState, BigInteger.valueOf(0), state);
			automaton.addInternalTransition(predState, BigInteger.valueOf(1), state);
			
			if (i == cInt - 1)
				automaton.addInternalTransition(state, BigInteger.valueOf(1), "final");
		}
		
		return new PairXY<NestedWordAutomaton<BigInteger, String>, List<Term>>(automaton, mapping);
	}

	/*
	 * Examples.
	 * TODO: Remove later.
	 */
	private void constructAutomaton() throws AutomataLibraryException
	{
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
	 * Examples.
	 * TODO: Remove later.
	 */
	private void someAuxiliaryMethodsThatMightBeHelpfulForWorkingWithFormulas()
	{
		final Term term = null;
		final Term term2 = null;
		SmtUtils.isAtomicFormula(term);
		SmtUtils.and(this, term, term2);
		final QuantifiedFormula qf = (QuantifiedFormula) term;
		SmtUtils.quantifier(this, QuantifiedFormula.EXISTS, new HashSet<TermVariable>(Arrays.asList(qf.getFreeVars())), term);
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
		
		
		/*
		Dirty test of how to walk to bottom in the tree.
		
		mLogger.info("term: " + term);
		mLogger.info("smtlib type: " + term.getSort());
		
		term = ((QuantifiedFormula)term).getSubformula();
		mLogger.info("term: " + term);
		mLogger.info("smtlib type: " + term.getSort());

		ApplicationTerm appTerm = (ApplicationTerm)term;
		mLogger.info("function: " + appTerm.getFunction().getName());
		
		Term[] terms = appTerm.getParameters();
		mLogger.info("term: " + terms[0]);
		mLogger.info("smtlib type: " + terms[0].getSort());
		
		appTerm = (ApplicationTerm)terms[0];
		mLogger.info("function: " + appTerm.getFunction().getName());
		
		terms = appTerm.getParameters();
		mLogger.info("term: " + terms[1]);
		mLogger.info("smtlib type: " + terms[1].getSort());
		mLogger.info("is smtlib type == Int: " + terms[1].getSort().getName().equals("Int"));
		*/
		
		/*
		ApplicationTerm		:= function symbols
		ConstantTerm		:= literals
		QuantifiedFormula	:=
		TermVariable		:= quantified variables
		*/
	}
}
