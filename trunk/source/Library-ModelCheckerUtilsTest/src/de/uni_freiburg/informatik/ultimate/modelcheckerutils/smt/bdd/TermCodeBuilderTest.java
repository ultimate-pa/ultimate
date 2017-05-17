package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.Arrays;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class TermCodeBuilderTest {

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

		script.setLogic(Logics.QF_AUFLIRA);
		bool = ((SMTInterpol) script).getTheory().getBooleanSort();
		ints = ((SMTInterpol) script).getTheory().getNumericSort();
	}

	@Test
	public void testVariables() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term x3 = script.variable("x3", bool);
		final Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1, x2, x3)), x1));

		/*
		 * Was folgt ider der code von TermCodeBuilder.printCode(t); falls du ne bessere idee hast wie man das testet:
		 * nur zu!
		 */
		final Sort sort_Bool = SmtSortUtils.getBoolSort(script);

		final Term var_x1 = script.variable("x1", sort_Bool);
		final Term var_x3 = script.variable("x3", sort_Bool);
		final Term var_x2 = script.variable("x2", sort_Bool);

		final Term term = script.term("or", script.term("and", var_x1, var_x2, var_x3), var_x1);
		// END generated code

		Assert.assertEquals(t, term);
	}

	@Test
	public void testLet() {
		final TermVariable x1 = script.variable("x1", ints);
		final Term d_7 = script.decimal("7");
		final Term d_3 = script.decimal("3");
		final Term t = script.let(new TermVariable[] { x1 }, new Term[] { d_7 }, script.term("<", d_3, x1));

		/*
		 * Was folgt ider der code von TermCodeBuilder.printCode(t); falls du ne bessere idee hast wie man das testet:
		 * nur zu!
		 */
		// TermCodeBuilder.printCode(t);
		// Sorts
		final Sort sort_Bool = SmtSortUtils.getBoolSort(script);
		final Sort sort_Real = SmtSortUtils.getRealSort(script);
		final Sort sort_Int = SmtSortUtils.getIntSort(script);

		// Constants
		final Term con_2171 = script.decimal("7.0");
		final Term con_931 = script.decimal("3.0");

		// Vars
		final TermVariable var_x1 = script.variable("x1", sort_Int);

		// Functions

		// term
		final Term term =
				script.let(new TermVariable[] { var_x1 }, new Term[] { con_2171 }, script.term("<", con_931, var_x1));
		// END generated code

		Assert.assertEquals(t, term);
	}

	@Test
	public void testRealWoldOne() {
		script.declareFun("noMemleak_a", new Sort[] {}, ints);
		script.declareFun("noMemleak_b", new Sort[] {}, ints);
		script.declareFun("v_noMemleak_a_3", new Sort[] {}, ints);
		script.declareFun("select2", new Sort[] { ints, ints }, bool);
		script.declareFun("store2", new Sort[] { ints, ints, bool }, ints);

		final Term a = script.term("noMemleak_a");
		final Term b = script.term("noMemleak_b");
		final Term a_3 = script.term("v_noMemleak_a_3");
		final Term v7 = script.numeral("7");
		final Term vTrue = script.term("true");
		final Term vFalse = script.term("false");

		final Term s1 = script.term("store2", a_3, v7, vTrue);
		final Term s2 = script.term("store2", s1, v7, vFalse);
		final Term e1 = script.term("=", a, s2);

		final Term s3 = script.term("select2", a_3, v7);

		final Term e2 = SmtUtils.not(script, script.term("=", b, a_3));

		final Term t = script.term("and", e2, s3, e1);

		/*
		 * Was folgt ider der code von TermCodeBuilder.printCode(t); falls du ne bessere idee hast wie man das testet:
		 * nur zu!
		 */
		// TermCodeBuilder.printCode(t);

		// Sorts
		final Sort sort_Bool = SmtSortUtils.getBoolSort(script);
		final Sort sort_Int = SmtSortUtils.getIntSort(script);

		// Constants
		final Term con_7 = script.numeral("7");

		// Vars

		// Functions
		// script.declareFun("v_noMemleak_a_3", new Sort[]{}, sort_Int);
		// script.declareFun("select2", new Sort[]{sort_Int, sort_Int}, sort_Bool);
		// script.declareFun("noMemleak_a", new Sort[]{}, sort_Int);
		// script.declareFun("noMemleak_b", new Sort[]{}, sort_Int);
		// script.declareFun("store2", new Sort[]{sort_Int, sort_Int, sort_Bool}, sort_Int);

		// term
		final Term term = script.term("and",
				script.term("not", script.term("=", script.term("noMemleak_b"), script.term("v_noMemleak_a_3"))),
				script.term("select2", script.term("v_noMemleak_a_3"), con_7),
				script.term("=", script.term("noMemleak_a"),
						script.term("store2",
								script.term("store2", script.term("v_noMemleak_a_3"), con_7, script.term("true")),
								con_7, script.term("false"))));
		// END generated code

		Assert.assertEquals(t, term);
	}

	/* quantifier kann interpol nich, rest sollte ich gerade mit gecheckt haben */
}
