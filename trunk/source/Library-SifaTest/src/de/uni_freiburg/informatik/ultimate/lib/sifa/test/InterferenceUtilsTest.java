package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public class InterferenceUtilsTest {

	private Script mScript;
	private Sort mIntSort;

	@Before
	public void setUp() {
		mScript = new SMTInterpol(new DefaultLogger());
		mScript.setLogic(Logics.ALL);
		mIntSort = mScript.sort("Int");
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	@Test
	public void collectConjunctsFlattensNestedAnds() {
		final TermVariable loc = mScript.variable("loc", mIntSort);
		final TermVariable x = mScript.variable("x", mIntSort);
		final TermVariable y = mScript.variable("y", mIntSort);
		final Term nested =
				mScript.term("and", eq(loc, num(1)), mScript.term("and", eq(x, num(2)), eq(y, num(3))));
		final List<Term> conjuncts = new ArrayList<>();

		collectConjuncts(nested, conjuncts);

		assertEquals(3, conjuncts.size());
	}

	@Test
	public void getTopLevelDisjunctsSplitsOnlyOuterOr() {
		final TermVariable loc = mScript.variable("loc", mIntSort);
		final Term nested = mScript.term("or", eq(loc, num(1)), mScript.term("or", eq(loc, num(2)), eq(loc, num(3))));

		assertEquals(2, SmtUtils.getDisjuncts(nested).length);
	}

	private static void collectConjuncts(final Term formula, final List<Term> result) {
		final Term[] conjuncts = SmtUtils.getConjuncts(formula);
		if (conjuncts.length == 1 && conjuncts[0] == formula) {
			result.add(formula);
			return;
		}
		for (final Term conjunct : conjuncts) {
			collectConjuncts(conjunct, result);
		}
	}

	private Term eq(final Term lhs, final Term rhs) {
		return SmtUtils.binaryEquality(mScript, lhs, rhs);
	}

	private Term num(final int value) {
		return mScript.numeral(Integer.toString(value));
	}
}
