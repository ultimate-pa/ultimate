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

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

@RunWith(JUnit4.class)
public class InferenceTest {
	private final Script mScript;
	private final Set<TermVariable> mTvs;
	// (g (ite (P&Q) x y))
	private final Term mTopLevel;
	// P&(g (ite (P&Q) x y))
	private final Term mSubLevel;
	// (g (f (ite (P&Q) x y) (ite (P||Q) y x)))
	private final Term mDouble;
	// (g (ite (P&Q) x (ite (P||Q) y x)))
	private final Term mNested;

	public InferenceTest() throws SMTLIBException {
		mScript = new NoopScript();
		mScript.setLogic(Logics.AUFLIA);
		// ITE-Lifting
		mScript.declareSort("U", 0);
		final Sort u = mScript.sort("U");
		final Sort[] binU = new Sort[] { u, u };
		final Sort[] singU = new Sort[] { u };
		final Sort[] emptysorts = new Sort[0];
		final Sort bool = mScript.sort("Bool");
		mScript.declareFun("f", binU, u);
		mScript.declareFun("g", singU, bool);
		final TermVariable x = mScript.variable("x", u);
		final TermVariable y = mScript.variable("y", u);
		mScript.declareFun("P", emptysorts, bool);
		mScript.declareFun("Q", emptysorts, bool);
		final Term pandq = mScript.term("and", mScript.term("P"), mScript.term("Q"));
		final Term porq = mScript.term("or", mScript.term("P"), mScript.term("Q"));

		final Term ite1 = mScript.term("ite", pandq, x, y);
		final Term ite2 = mScript.term("ite", porq, y, x);
		mTopLevel = mScript.term("g", ite1);
		mSubLevel = mScript.term("and", mScript.term("P"), mTopLevel);
		mDouble = mScript.term("g", mScript.term("f", ite1, ite2));
		mNested = mScript.term("g", mScript.term("ite", pandq, x, ite2));
		mTvs = new HashSet<>();
		mTvs.add(x);
		mTvs.add(y);
	}

	@Test
	public void testITELifting() {
		final InferencePreparation ip = new InferencePreparation(mTopLevel.getTheory(), mTvs);
		Assert.assertEquals("(ite (and P Q) (g x) (g y))", ip.prepare(mTopLevel).toStringDirect());
		Assert.assertEquals("(and P (ite (and P Q) (g x) (g y)))", ip.prepare(mSubLevel).toStringDirect());
		Assert.assertEquals(
				"(ite (and P Q) (ite (or P Q) (g (f x y)) (g (f x x))) (ite (or P Q) (g (f y y)) (g (f y x))))", // NOCHECKSTYLE
				ip.prepare(mDouble).toStringDirect());
		Assert.assertEquals("(ite (and P Q) (g x) (ite (or P Q) (g y) (g x)))", ip.prepare(mNested).toStringDirect());
	}

	@Test
	public void testPatternInference() {
		// Pattern inference
		final Sort bool = mScript.sort("Bool");
		final Sort u = mScript.sort("U");
		final Sort[] binU = new Sort[] { u, u };
		final Sort[] singU = new Sort[] { u };
		final TermVariable x = mScript.variable("x", u);
		final TermVariable y = mScript.variable("y", u);
		final TermVariable z = mScript.variable("z", u);
		mScript.declareFun("T", binU, bool);
		mScript.declareFun("h", singU, u);
		mScript.declareFun("k", singU, u);
		Term loopingtrig, nonloopingtrig;
		// (forall ((x U)) (T (h x) (h (k x)))) Simplify tech report page 44
		final Term looping = mScript.quantifier(Script.FORALL, new TermVariable[] { x }, mScript.term("T",
				loopingtrig = mScript.term("h", x), mScript.term("h", nonloopingtrig = mScript.term("k", x))));
		final Set<TermVariable> singleX = Collections.singleton(x);
		Term c, p1, p2;
		// (forall ((x U) (y U) (z U)) (implies (and (T x y) (T y z)) (T x z)))
		final Term transitivity = mScript.quantifier(Script.FORALL, new TermVariable[] { x, y, z },
				mScript.term("=>", mScript.term("and", p1 = mScript.term("T", x, y), p2 = mScript.term("T", y, z)),
						c = mScript.term("T", x, z)));
		final Set<TermVariable> transitivityVars = new HashSet<>();
		transitivityVars.add(x);
		transitivityVars.add(y);
		transitivityVars.add(z);
		mScript.declareFun("a", new Sort[0], u);
		final Term fa = mScript.term("a");
		// (forall ((x U)) (and (T a a) (T a x)))
		Term constTrig;
		final Term partiallyConstant = mScript.quantifier(Script.FORALL, new TermVariable[] { x },
				mScript.term("and", mScript.term("T", fa, fa), constTrig = mScript.term("T", fa, x)));
		// (forall ((i1 Int) (i2 Int)) (= (+ (* 3 i1) (* 5 i2)) 0))
		final Sort intSort = mScript.sort("Int");
		final TermVariable i1 = mScript.variable("i1", intSort);
		final TermVariable i2 = mScript.variable("i2", intSort);
		// (forall ((i1 Int) (i2 Int)) (= (+ (* 3 i1) (* 5 i2)) 0))
		final Term notrig = mScript.quantifier(Script.FORALL, new TermVariable[] { i1, i2 },
				mScript.term("=", mScript.term("+", mScript.term("*", mScript.numeral("3"), i1),
						mScript.term("*", mScript.numeral("5"), i2)), mScript.numeral("0")));
		final Set<TermVariable> intvars = new HashSet<>();
		intvars.add(i1);
		intvars.add(i2);
		mScript.declareFun("fi", new Sort[] { intSort }, intSort);
		// (forall ((i1 Int)) (= (fi (+ (* 3 i1) 7)) 5))
		final Term notrigcomb =
				mScript.quantifier(Script.FORALL, new TermVariable[] { i1 },
						mScript.term("=", mScript.term("fi",
								mScript.term("+", mScript.term("*", mScript.numeral("3"), i1), mScript.numeral("7"))),
								mScript.numeral("10")));
		final Set<TermVariable> int1 = Collections.singleton(i1);

		final LogProxy logger = new DefaultLogger();
		final TriggerCandidateMap candidates = new TriggerCandidateMap(logger, mTopLevel.getTheory(), singleX);
		candidates.insert(((QuantifiedFormula) looping).getSubformula());
		Term[] units = candidates.getAllUnitTriggers();
		// This formula has at least one unit-trigger
		Assert.assertNotNull(units);
		logger.info("For " + looping + " I inferred unit triggers " + Arrays.toString(units));
		final int expectedLength = Config.FEATURE_BLOCK_LOOPING_PATTERN ? 1 : 2;
		final Set<Term> unitSet = new HashSet<>(expectedLength, 1.0f);
		for (final Term t : units) {
			unitSet.add(t);
		}
		Assert.assertEquals(expectedLength, unitSet.size());
		Assert.assertTrue("Did not infer nonlooping trigger (k x)", unitSet.contains(nonloopingtrig));
		if (!Config.FEATURE_BLOCK_LOOPING_PATTERN) {
			Assert.assertTrue("Did not infer looping trigger (h x) although I should", unitSet.contains(loopingtrig));
		}
		candidates.reinit(transitivityVars);
		candidates.insert(((QuantifiedFormula) transitivity).getSubformula());
		units = candidates.getAllUnitTriggers();
		// This formula only has multi-triggers
		Assert.assertNull(units);
		Term[] multi = candidates.getMultiTrigger();
		Assert.assertNotNull(multi);
		logger.info("For " + transitivity + " I inferred multi trigger " + Arrays.toString(multi));
		final Set<Term> multiSet = new HashSet<>(2, 1.0f);
		for (final Term t : multi) {
			multiSet.add(t);
		}
		Assert.assertEquals(2, multiSet.size());
		final Iterator<Term> it = multiSet.iterator();
		final Term first = it.next();
		final Term second = it.next();
		if (first == p1) {
			Assert.assertTrue("Wrong multi trigger", second == p2 || second == c);
		} else if (first == p2) {
			Assert.assertTrue("Wrong multi trigger", second == p1 || second == c);
		} else if (first == c) {
			Assert.assertTrue("Wrong multi trigger", second == p1 || second == p2);
		}
		candidates.reinit(singleX);
		candidates.insert(((QuantifiedFormula) partiallyConstant).getSubformula());
		units = candidates.getAllUnitTriggers();
		Assert.assertNotNull(units);
		logger.info("For " + partiallyConstant + " I inferred unit triggers " + Arrays.toString(units));
		Assert.assertEquals(1, units.length);
		Assert.assertEquals(constTrig, units[0]);
		candidates.reinit(intvars);
		candidates.insert(((QuantifiedFormula) notrig).getSubformula());
		units = candidates.getAllUnitTriggers();
		Assert.assertNull("Did infer unit-triggers where none exists: " + Arrays.toString(units), units);
		multi = candidates.getMultiTrigger();
		Assert.assertNull("Did infer a multi trigger where none exists: " + Arrays.toString(multi), multi);
		candidates.reinit(int1);
		candidates.insert(((QuantifiedFormula) notrigcomb).getSubformula());
		units = candidates.getAllUnitTriggers();
		Assert.assertNull("Did infer unit-triggers where none exists: " + Arrays.toString(units), units);
		multi = candidates.getMultiTrigger();
		Assert.assertNull("Did infer a multi trigger where none exists: " + Arrays.toString(multi), multi);
	}
}
