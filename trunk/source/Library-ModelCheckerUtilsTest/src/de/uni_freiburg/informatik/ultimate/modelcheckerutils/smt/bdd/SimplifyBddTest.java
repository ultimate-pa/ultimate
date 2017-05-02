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

	IUltimateServiceProvider services;
	Script script;
	SimplifyBdd simplifyBdd;
	Sort bool;
	Sort ints;

	@Before
	public void setUP() {
		services = UltimateMocks.createUltimateServiceProviderMock();
		script = new SMTInterpol();
		final ManagedScript mgdScript = new ManagedScript(services, script);
		simplifyBdd = new SimplifyBdd(services, mgdScript);

		script.setLogic(Logics.QF_UFIDL);
		bool = ((SMTInterpol) script).getTheory().getBooleanSort();
		ints = ((SMTInterpol) script).getTheory().getNumericSort();
	}

	@Test
	public void testAtomCollection() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term x3 = script.variable("x3", bool);
		final Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1, x2, x3)), x1));

		final CollectAtoms ca = new CollectAtoms();
		final List<Term> atoms = ca.getTerms(t);
		Assert.assertTrue(atoms.contains(x1));
		Assert.assertTrue(atoms.contains(x2));
		Assert.assertTrue(atoms.contains(x3));
		Assert.assertEquals(3, atoms.size());
	}

	@Test
	public void testTransform() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term x3 = script.variable("x3", bool);
		final Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1, x2, x3)), x1));
		final Term out = simplifyBdd.transform(t);
		Assert.assertEquals(x1, out);
	}

	@Test
	public void testCNF() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term x3 = script.variable("x3", bool);
		final Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1, x2, x3)), x1));
		final Term out = simplifyBdd.transformToCNF(t);
		Assert.assertEquals(x1, out);
	}

	@Test
	public void testDNF() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term x3 = script.variable("x3", bool);
		final Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1, x2, x3)), x1));
		final Term out = simplifyBdd.transformToDNF(t);
		Assert.assertEquals(x1, out);
	}

	@Test
	public void testAssozImp() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term x3 = script.variable("x3", bool);
		final Term t1 = script.term("=>", x1, x2, x3);
		final Term t2 = script.term("=>", x1, script.term("=>", x2, x3));
		final Term t3 = script.term("=>", script.term("=>", x1, x2), x3);

		final Term out1 = simplifyBdd.transform(t1);
		final Term out2 = simplifyBdd.transform(t2);
		final Term out3 = simplifyBdd.transform(t3);
		Assert.assertEquals(out2, out1);
		Assert.assertNotEquals(out3, out1);
	}

	@Test
	public void testPairImp() {
		final Term t1 = script.term("<", script.numeral("1"), script.numeral("2"));
		final Term t2 = script.term("<", script.numeral("1"), script.numeral("3"));
		simplifyBdd.impliesPairwise(Arrays.asList(t1, t2));
	}

	@Test
	public void testWithImplications() {
		script.declareFun("noMemleak_a", new Sort[] {}, ints);
		script.declareFun("noMemleak_b", new Sort[] {}, ints);
		script.declareFun("v_noMemleak_a_3", new Sort[] {}, ints);
		script.declareFun("select", new Sort[] { ints, ints }, bool);
		script.declareFun("store", new Sort[] { ints, ints, bool }, ints);

		final Term a = script.term("noMemleak_a");
		final Term b = script.term("noMemleak_b");
		final Term a_3 = script.term("v_noMemleak_a_3");
		final Term v7 = script.numeral("7");
		final Term vTrue = script.term("true");
		final Term vFalse = script.term("false");

		final Term s1 = script.term("store", a_3, v7, vTrue);
		final Term s2 = script.term("store", s1, v7, vFalse);
		final Term e1 = script.term("=", a, s2);

		final Term s3 = script.term("select", a_3, v7);

		// Term e2 = SmtUtils.not(script, script.term("=", b, a_3));
		final Term e2 = script.term("=", b, a_3);

		final Term and = script.term("and", e2, s3, e1);

		final Term out = simplifyBdd.transformWithImplications(and);
		System.out.println(out + "\n" + and);

	}

	@Test
	public void testWeirdStuff() {
		script.declareFun("noMemleak_a", new Sort[] {}, ints);
		script.declareFun("noMemleak_b", new Sort[] {}, ints);
		script.declareFun("v_noMemleak_a_3", new Sort[] {}, ints);
		script.declareFun("select", new Sort[] { ints, ints }, bool);
		script.declareFun("store", new Sort[] { ints, ints, bool }, ints);

		final Term a = script.term("noMemleak_a");
		final Term b = script.term("noMemleak_b");
		final Term a_3 = script.term("v_noMemleak_a_3");
		final Term v7 = script.numeral("7");
		final Term vTrue = script.term("true");
		final Term vFalse = script.term("false");

		final Term s1 = script.term("store", a_3, v7, vTrue);
		final Term s2 = script.term("store", s1, v7, vFalse);
		final Term e1 = script.term("=", a, s2);

		final Term s3 = script.term("select", a_3, v7);

		// Term e2 = SmtUtils.not(script, script.term("=", b, a_3));
		final Term e2 = script.term("=", b, a_3);

		final Term and = script.term("and", e2, s3, e1);

		final Term out = simplifyBdd.transformToDNF(and);
		Assert.assertTrue(and + " got in and that got out " + out,
				Util.checkSat(script, script.term("distinct", and, out)) != LBool.SAT);

		/*
		 * (and (not (= noMemleak_b v_noMemleak_a_3) ) (select v_noMemleak_a_3 7) (= noMemleak_a (store (store
		 * v_noMemleak_a_3 7 true) 7 false)) )
		 */

	}

	@Test
	public void bugSimplification20161108() {
		// Sorts
		final Sort sort_Bool = script.sort("Bool");
		// Vars
		final TermVariable t = script.variable("main_#t~switch0", sort_Bool);
		// term
		final Term term = script.term("not", t);
		final Term out = simplifyBdd.transform(term);

		Assert.assertTrue("simplification unsound. Input: " + term,
				Util.checkSat(script, script.term("distinct", term, out)) != LBool.SAT);
	}

}
