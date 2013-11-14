/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import junit.framework.TestCase;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public class InferenceTest extends TestCase {
	private Script m_Script;
	private Set<TermVariable> m_tvs;
	// (g (ite (P&Q) x y))
	private Term m_topLevel;
	// P&(g (ite (P&Q) x y))
	private Term m_subLevel;
	// (g (f (ite (P&Q) x y) (ite (P||Q) y x)))
	private Term m_double;
	// (g (ite (P&Q) x (ite (P||Q) y x)))
	private Term m_nested;
	// (forall ((x U)) (T (h x) (h (k x)))) Simplify tech report page 44
	private Term m_looping;
	private Term m_nonloopingtrig;
	private Term m_loopingtrig;
	private Set<TermVariable> m_singleX;
	// (forall ((x U) (y U) (z U)) (implies (and (T x y) (T y z)) (T x z)))
	private Term m_transitivity;
	private Set<TermVariable> m_transitivityVars;
	private Term m_p1;
	private Term m_p2;
	private Term m_c;
	// (forall ((x U)) (and (T a a) (T a x)))
	private Term m_partiallyConstant;
	private Term m_constTrig;
	// (forall ((i1 Int) (i2 Int)) (= (+ (* 3 i1) (* 5 i2)) 0))
	private Term m_notrig;
	private Set<TermVariable> m_intvars;
	// (forall ((i1 Int)) (= (fi (+ (* 3 i1) 7)) 5))
	private Term m_notrigcomb;
	private Set<TermVariable> m_i1;
	
	public InferenceTest() throws SMTLIBException {
		m_Script = new SMTInterpol(Logger.getRootLogger());
		m_Script.setLogic(Logics.QF_UFLIA);
		// ITE-Lifting
		m_Script.declareSort("U", 0);
		Sort u = m_Script.sort("U");
		Sort[] binU = new Sort[] { u,u };
		Sort[] singU = new Sort[] { u };
		Sort[] emptysorts = new Sort[0];
		Sort bool = m_Script.sort("Bool");
		m_Script.declareFun("f", binU, u);
		m_Script.declareFun("g", singU, bool);
		TermVariable x = m_Script.variable("x", u);
		TermVariable y = m_Script.variable("y", u);
		m_Script.declareFun("P", emptysorts, bool);
		m_Script.declareFun("Q", emptysorts, bool);
		Term pandq = m_Script.term("and",
				m_Script.term("P"), m_Script.term("Q"));
		Term porq = m_Script.term("or", m_Script.term("P"), m_Script.term("Q"));
		
		Term ite1 = m_Script.term("ite", pandq, x, y);
		Term ite2 = m_Script.term("ite", porq, y, x);
		m_topLevel = m_Script.term("g",ite1);
		m_subLevel = m_Script.term("and", m_Script.term("P"),m_topLevel);
		m_double = m_Script.term("g",m_Script.term("f",ite1,ite2));
		m_nested = m_Script.term("g",m_Script.term("ite", pandq, x, ite2));
		m_tvs = new HashSet<TermVariable>();
		m_tvs.add(x);
		m_tvs.add(y);
	}
	public void testITELifting() {
		InferencePreparation ip = new InferencePreparation(m_topLevel.getTheory(),m_tvs);
		assertEquals("(ite (and P Q) (g x) (g y))",ip.prepare(m_topLevel).toStringDirect());
		assertEquals("(and P (ite (and P Q) (g x) (g y)))",ip.prepare(m_subLevel).toStringDirect());
		assertEquals("(ite (and P Q) (ite (or P Q) (g (f x y)) (g (f x x))) (ite (or P Q) (g (f y y)) (g (f y x))))",ip.prepare(m_double).toStringDirect());
		assertEquals("(ite (and P Q) (g x) (ite (or P Q) (g y) (g x)))",ip.prepare(m_nested).toStringDirect());
	}
	public void testPatternInference() {
		if (true)
			return;
		// Pattern inference
		Sort bool = m_Script.sort("Bool");
		Sort u = m_Script.sort("U");
		Sort[] binU = new Sort[] { u,u };
		Sort[] singU = new Sort[] { u };
		TermVariable x = m_Script.variable("x", u);
		TermVariable y = m_Script.variable("y", u);
		TermVariable z = m_Script.variable("z", u);
		m_Script.declareFun("T", binU, bool);
		m_Script.declareFun("h", singU, u);
		m_Script.declareFun("k", singU, u);
		m_looping = m_Script.quantifier(Script.FORALL, new TermVariable[]{x}, 
				m_Script.term("T", 
						m_loopingtrig = m_Script.term("h",x), 
						m_Script.term("h",
								m_nonloopingtrig = m_Script.term("k",x))));
		m_singleX = Collections.singleton(x);
		m_transitivity = m_Script.quantifier(Script.FORALL,
				new TermVariable[]{x,y,z},
				m_Script.term("=>",
						m_Script.term("and",
								m_p1 = m_Script.term("T",x,y),
								m_p2 = m_Script.term("T",y,z)),
						m_c = m_Script.term("T",x,z)));
		m_transitivityVars = new HashSet<TermVariable>();
		m_transitivityVars.add(x);
		m_transitivityVars.add(y);
		m_transitivityVars.add(z);
		m_Script.declareFun("a", new Sort[0], u);
		Term fa = m_Script.term("a");
		// (forall ((x U)) (and (T a a) (T a x)))
		m_partiallyConstant = m_Script.quantifier(Script.FORALL, 
				new TermVariable[]{x}, 
				m_Script.term("and",
						m_Script.term("T",fa,fa),
						m_constTrig = m_Script.term("T",fa,x)));
		// (forall ((i1 Int) (i2 Int)) (= (+ (* 3 i1) (* 5 i2)) 0))
		Sort intSort = m_Script.sort("Int");
		TermVariable i1 = m_Script.variable("i1", intSort);
		TermVariable i2 = m_Script.variable("i2", intSort);
		m_notrig = m_Script.quantifier(Script.FORALL, new TermVariable[]{i1,i2},
				m_Script.term("=",
						m_Script.term("+",
								m_Script.term("*",
										m_Script.numeral("3"),
										i1),
								m_Script.term("*",
										m_Script.numeral("5"),
										i2)),
						m_Script.numeral("0")));
		m_intvars = new HashSet<TermVariable>();
		m_intvars.add(i1);
		m_intvars.add(i2);
		m_Script.declareFun("fi", new Sort[]{intSort}, intSort);
		m_notrigcomb = m_Script.quantifier(Script.FORALL, new TermVariable[]{i1},
				m_Script.term("=", 
						m_Script.term("fi",
								m_Script.term("+",
										m_Script.term("*",
												m_Script.numeral("3"),
												i1),
										m_Script.numeral("7"))),
						m_Script.numeral("10")));
		m_i1 = Collections.singleton(i1);

		Logger logger = Logger.getRootLogger();
		TriggerCandidateMap candidates = new TriggerCandidateMap(
				logger,m_topLevel.getTheory(),m_singleX);
		candidates.insert(((QuantifiedFormula)m_looping).getSubformula());
		Term[] units = candidates.getAllUnitTriggers();
		// This formula has at least one unit-trigger
		assertNotNull(units);
		logger.info("For " + m_looping + " I inferred unit triggers " + 
				Arrays.toString(units));
		int expectedLength = Config.FEATURE_BLOCK_LOOPING_PATTERN ? 1 : 2;
		Set<Term> unitSet = new HashSet<Term>(expectedLength,1.0f);
		for (Term t : units)
			unitSet.add(t);
		assertEquals(expectedLength,unitSet.size());
		assertTrue("Did not infer nonlooping trigger (k x)",
				unitSet.contains(m_nonloopingtrig));
		if (!Config.FEATURE_BLOCK_LOOPING_PATTERN)
			assertTrue("Did not infer looping trigger (h x) although I should",
					unitSet.contains(m_loopingtrig));
		candidates.reinit(m_transitivityVars);
		candidates.insert(((QuantifiedFormula)m_transitivity).getSubformula());
		units = candidates.getAllUnitTriggers();
		// This formula only has multi-triggers
		assertNull(units);
		Term[] multi = candidates.getMultiTrigger();
		assertNotNull(multi);
		logger.info("For " + m_transitivity + " I inferred multi trigger " + 
				Arrays.toString(multi));
		Set<Term> multiSet = new HashSet<Term>(2,1.0f);
		for (Term t : multi)
			multiSet.add(t);
		assertEquals(2, multiSet.size());
		Iterator<Term> it = multiSet.iterator();
		Term first = it.next();
		Term second = it.next();
		if (first == m_p1)
			assertTrue("Wrong multi trigger", second == m_p2 || second == m_c);
		else if (first == m_p2)
			assertTrue("Wrong multi trigger", second == m_p1 || second == m_c);
		else if (first == m_c)
			assertTrue("Wrong multi trigger", second == m_p1 || second == m_p2);
		candidates.reinit(m_singleX);
		candidates.insert(
				((QuantifiedFormula)m_partiallyConstant).getSubformula());
		units = candidates.getAllUnitTriggers();
		assertNotNull(units);
		logger.info("For " + m_partiallyConstant + " I inferred unit triggers " + 
				Arrays.toString(units));
		assertEquals(1, units.length);
		assertEquals(m_constTrig, units[0]);
		candidates.reinit(m_intvars);
		candidates.insert(((QuantifiedFormula)m_notrig).getSubformula());
		units = candidates.getAllUnitTriggers();
		assertNull("Did infer unit-triggers where none exists: " + Arrays.toString(units),units);
		multi = candidates.getMultiTrigger();
		assertNull("Did infer a multi trigger where none exists: " + Arrays.toString(multi),multi);
		candidates.reinit(m_i1);
		candidates.insert(((QuantifiedFormula)m_notrigcomb).getSubformula());
		units = candidates.getAllUnitTriggers();
		assertNull("Did infer unit-triggers where none exists: " + Arrays.toString(units),units);
		multi = candidates.getMultiTrigger();
		assertNull("Did infer a multi trigger where none exists: " + Arrays.toString(multi),multi);
	}
}
