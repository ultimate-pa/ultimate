/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Tests for {@link SimplifyBdd}
 *
 * @author Michael Steinle
 *
 */
public class SimplifyBddTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private SimplifyBdd mSimplifyBdd;
	private Sort mBool;
	private Sort mInts;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = new SMTInterpol();
		final ManagedScript mgdScript = new ManagedScript(mServices, mScript);
		mSimplifyBdd = new SimplifyBdd(mServices, mgdScript);
		mScript.setLogic(Logics.QF_UFIDL);
		mBool = SmtSortUtils.getBoolSort(mgdScript);
		mInts = SmtSortUtils.getIntSort(mgdScript);
	}

	public void tearDown() {
		mScript.exit();
	}

	@Test
	public void testAtomCollection() {
		final Term x1 = mScript.variable("x1", mBool);
		final Term x2 = mScript.variable("x2", mBool);
		final Term x3 = mScript.variable("x3", mBool);
		final Term t = SmtUtils.or(mScript, Arrays.asList(SmtUtils.and(mScript, Arrays.asList(x1, x2, x3)), x1));

		final CollectAtoms ca = new CollectAtoms();
		final List<Term> atoms = ca.getTerms(t);
		Assert.assertTrue(atoms.contains(x1));
		Assert.assertTrue(atoms.contains(x2));
		Assert.assertTrue(atoms.contains(x3));
		Assert.assertEquals(3, atoms.size());
	}

	@Test
	public void testTransform() {
		final Term x1 = mScript.variable("x1", mBool);
		final Term x2 = mScript.variable("x2", mBool);
		final Term x3 = mScript.variable("x3", mBool);
		final Term t = SmtUtils.or(mScript, Arrays.asList(SmtUtils.and(mScript, Arrays.asList(x1, x2, x3)), x1));
		final Term out = mSimplifyBdd.transform(t);
		Assert.assertEquals(x1, out);
	}

	@Test
	public void testCNF() {
		final Term x1 = mScript.variable("x1", mBool);
		final Term x2 = mScript.variable("x2", mBool);
		final Term x3 = mScript.variable("x3", mBool);
		final Term t = SmtUtils.or(mScript, Arrays.asList(SmtUtils.and(mScript, Arrays.asList(x1, x2, x3)), x1));
		final Term out = mSimplifyBdd.transformToCNF(t);
		Assert.assertEquals(x1, out);
	}

	@Test
	public void testDNF() {
		final Term x1 = mScript.variable("x1", mBool);
		final Term x2 = mScript.variable("x2", mBool);
		final Term x3 = mScript.variable("x3", mBool);
		final Term t = SmtUtils.or(mScript, Arrays.asList(SmtUtils.and(mScript, Arrays.asList(x1, x2, x3)), x1));
		final Term out = mSimplifyBdd.transformToDNF(t);
		Assert.assertEquals(x1, out);
	}

	@Test
	public void testAssozImp() {
		final Term x1 = mScript.variable("x1", mBool);
		final Term x2 = mScript.variable("x2", mBool);
		final Term x3 = mScript.variable("x3", mBool);
		final Term t1 = mScript.term("=>", x1, x2, x3);
		final Term t2 = mScript.term("=>", x1, mScript.term("=>", x2, x3));
		final Term t3 = mScript.term("=>", mScript.term("=>", x1, x2), x3);

		final Term out1 = mSimplifyBdd.transform(t1);
		final Term out2 = mSimplifyBdd.transform(t2);
		final Term out3 = mSimplifyBdd.transform(t3);
		Assert.assertEquals(out2, out1);
		Assert.assertNotEquals(out3, out1);
	}

	@Test
	public void testPairImp() {
		final Term t1 = mScript.term("<", mScript.numeral("1"), mScript.numeral("2"));
		final Term t2 = mScript.term("<", mScript.numeral("1"), mScript.numeral("3"));
		mSimplifyBdd.impliesPairwise(Arrays.asList(t1, t2));
	}

	@Test
	public void testWithImplications() {
		mScript.declareFun("noMemleak_a", new Sort[] {}, mInts);
		mScript.declareFun("noMemleak_b", new Sort[] {}, mInts);
		mScript.declareFun("v_noMemleak_a_3", new Sort[] {}, mInts);
		mScript.declareFun("select", new Sort[] { mInts, mInts }, mBool);
		mScript.declareFun("store", new Sort[] { mInts, mInts, mBool }, mInts);

		final Term a = mScript.term("noMemleak_a");
		final Term b = mScript.term("noMemleak_b");
		final Term a_3 = mScript.term("v_noMemleak_a_3");
		final Term v7 = mScript.numeral("7");
		final Term vTrue = mScript.term("true");
		final Term vFalse = mScript.term("false");

		final Term s1 = mScript.term("store", a_3, v7, vTrue);
		final Term s2 = mScript.term("store", s1, v7, vFalse);
		final Term e1 = mScript.term("=", a, s2);

		final Term s3 = mScript.term("select", a_3, v7);

		// Term e2 = SmtUtils.not(script, script.term("=", b, a_3));
		final Term e2 = mScript.term("=", b, a_3);

		final Term and = mScript.term("and", e2, s3, e1);

		final Term out = mSimplifyBdd.transformWithImplications(and);
		System.out.println(out + "\n" + and);

	}

	@Test
	public void testWeirdStuff() {
		mScript.declareFun("noMemleak_a", new Sort[] {}, mInts);
		mScript.declareFun("noMemleak_b", new Sort[] {}, mInts);
		mScript.declareFun("v_noMemleak_a_3", new Sort[] {}, mInts);
		mScript.declareFun("select", new Sort[] { mInts, mInts }, mBool);
		mScript.declareFun("store", new Sort[] { mInts, mInts, mBool }, mInts);

		final Term a = mScript.term("noMemleak_a");
		final Term b = mScript.term("noMemleak_b");
		final Term a_3 = mScript.term("v_noMemleak_a_3");
		final Term v7 = mScript.numeral("7");
		final Term vTrue = mScript.term("true");
		final Term vFalse = mScript.term("false");

		final Term s1 = mScript.term("store", a_3, v7, vTrue);
		final Term s2 = mScript.term("store", s1, v7, vFalse);
		final Term e1 = mScript.term("=", a, s2);

		final Term s3 = mScript.term("select", a_3, v7);

		// Term e2 = SmtUtils.not(script, script.term("=", b, a_3));
		final Term e2 = mScript.term("=", b, a_3);

		final Term and = mScript.term("and", e2, s3, e1);

		final Term out = mSimplifyBdd.transformToDNF(and);
		Assert.assertTrue(and + " got in and that got out " + out,
				Util.checkSat(mScript, mScript.term("distinct", and, out)) != LBool.SAT);

		/*
		 * (and (not (= noMemleak_b v_noMemleak_a_3) ) (select v_noMemleak_a_3 7) (= noMemleak_a (store (store
		 * v_noMemleak_a_3 7 true) 7 false)) )
		 */

	}

	@Test
	public void bugSimplification20161108() {
		// Sorts
		final Sort sort_Bool = SmtSortUtils.getBoolSort(mScript);
		// Vars
		final TermVariable t = mScript.variable("main_#t~switch0", sort_Bool);
		// term
		final Term term = mScript.term("not", t);
		final Term out = mSimplifyBdd.transform(term);

		Assert.assertTrue("simplification unsound. Input: " + term,
				Util.checkSat(mScript, mScript.term("distinct", term, out)) != LBool.SAT);
	}

}
