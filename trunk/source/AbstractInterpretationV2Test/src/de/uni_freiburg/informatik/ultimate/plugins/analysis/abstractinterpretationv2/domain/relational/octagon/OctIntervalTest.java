package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator.EvalResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;

public class OctIntervalTest {

	@Test
	public void testTopBottom() {
		final OctInterval top = new OctInterval(OctValue.INFINITY, OctValue.INFINITY);
		final OctInterval openRight = new OctInterval(OctValue.ZERO, OctValue.INFINITY);
		final OctInterval openLeft = new OctInterval(OctValue.INFINITY, OctValue.ZERO);
		final OctInterval point = new OctInterval(OctValue.parse("2.1"), OctValue.parse("2.10"));
		final OctInterval bot = new OctInterval(OctValue.parse("-1"), OctValue.parse("-1.1"));

		Assert.assertFalse(top.isBottom());
		Assert.assertTrue(top.isTop());
		Assert.assertFalse(openRight.isBottom());
		Assert.assertFalse(openRight.isTop());
		Assert.assertFalse(openLeft.isBottom());
		Assert.assertFalse(openLeft.isTop());
		Assert.assertFalse(point.isBottom());
		Assert.assertFalse(point.isTop());
		Assert.assertTrue(bot.isBottom());
		Assert.assertFalse(bot.isTop());
	}

	@Test
	public void testEvaluateTopBot() {
		final Rational rational2p1 = Rational.valueOf(21, 10);
		final Rational bigRational = Rational.valueOf(new BigInteger("-1234567890123456"), BigInteger.ONE);

		final OctInterval top = new OctInterval(OctValue.INFINITY, OctValue.INFINITY);
		final OctInterval bot = new OctInterval(OctValue.parse("7.3"), OctValue.parse("-2"));
		for (final RelationSymbol relSymb : RelationSymbol.values()) {
			testEval(EvalResult.UNKNOWN, top, relSymb, Rational.MONE);
			testEval(EvalResult.UNKNOWN, top, relSymb, Rational.ONE);
			testEval(EvalResult.UNKNOWN, top, relSymb, rational2p1);
			testEval(EvalResult.UNKNOWN, top, relSymb, bigRational);

			testEval(EvalResult.TRUE, bot, relSymb, Rational.MONE);
			testEval(EvalResult.TRUE, bot, relSymb, Rational.ONE);
			testEval(EvalResult.TRUE, bot, relSymb, rational2p1);
			testEval(EvalResult.TRUE, bot, relSymb, bigRational);
		}
	}

	@Test
	public void testEvaluateEq() {
		testEval(EvalResult.TRUE, "4.5", "4.5", RelationSymbol.EQ, "45/10");
		testEval(EvalResult.TRUE, "-23425621248345.2", "-23425621248345.2", RelationSymbol.EQ, "-234256212483452/10");
		testEval(EvalResult.FALSE, "-2", "4", RelationSymbol.EQ, "-201/100");
		testEval(EvalResult.FALSE, "-2", "4", RelationSymbol.EQ, "401/100");
		testEval(EvalResult.FALSE, "-2", "4", RelationSymbol.EQ, "1234567891234567/1");
		testEval(EvalResult.UNKNOWN, "-2", "4", RelationSymbol.EQ, "-2");
		testEval(EvalResult.UNKNOWN, "-2", "4", RelationSymbol.EQ, "3");
		testEval(EvalResult.UNKNOWN, "-2", "4", RelationSymbol.EQ, "4");
	}

	@Test
	public void testEvaluateDistinct() {
		testEval(EvalResult.TRUE, "2.11", "inf", RelationSymbol.DISTINCT, "21/10");
		testEval(EvalResult.TRUE, "-4", "2.09", RelationSymbol.DISTINCT, "21/10");
		testEval(EvalResult.TRUE, "inf", "2.09", RelationSymbol.DISTINCT, "21/10");
		testEval(EvalResult.FALSE, "55.1", "55.1", RelationSymbol.DISTINCT, "551/10");
		testEval(EvalResult.UNKNOWN, "2", "inf", RelationSymbol.DISTINCT, "21/10");
		testEval(EvalResult.UNKNOWN, "2.1", "inf", RelationSymbol.DISTINCT, "21/10");
	}

	@Test
	public void testEvaluateLeq() {
		testEval(EvalResult.TRUE, "2", "2.099", RelationSymbol.LEQ, "21/10");
		testEval(EvalResult.TRUE, "2", "2.100", RelationSymbol.LEQ, "21/10");
		testEval(EvalResult.UNKNOWN, "2", "2.101", RelationSymbol.LEQ, "21/10");

		testEval(EvalResult.UNKNOWN, "776", "inf", RelationSymbol.LEQ, "777");
		testEval(EvalResult.UNKNOWN, "777", "inf", RelationSymbol.LEQ, "777");
		testEval(EvalResult.FALSE, "778", "inf", RelationSymbol.LEQ, "777");

		testEval(EvalResult.TRUE, "-9734736690235", "-9734736690235", RelationSymbol.LEQ, "-9734736690234");
		testEval(EvalResult.TRUE, "-9734736690234", "-9734736690234", RelationSymbol.LEQ, "-9734736690234");
		testEval(EvalResult.FALSE, "-9734736690233", "-9734736690233", RelationSymbol.LEQ, "-9734736690234");
	}
	
	@Test
	public void testEvaluateLess() {
		testEval(EvalResult.TRUE, "2", "2.099", RelationSymbol.LESS, "21/10");
		testEval(EvalResult.UNKNOWN, "2", "2.100", RelationSymbol.LESS, "21/10");
		testEval(EvalResult.UNKNOWN, "2", "2.101", RelationSymbol.LESS, "21/10");

		testEval(EvalResult.UNKNOWN, "776", "inf", RelationSymbol.LESS, "777");
		testEval(EvalResult.FALSE, "777", "inf", RelationSymbol.LESS, "777");
		testEval(EvalResult.FALSE, "778", "inf", RelationSymbol.LESS, "777");

		testEval(EvalResult.TRUE, "-9734736690234.000000000100001", "-9734736690234.000000000100001",
				RelationSymbol.LESS, "-97347366902340000000001/10000000000");
		testEval(EvalResult.FALSE, "-9734736690234", "-9734736690234", RelationSymbol.LESS, "-9734736690234");
		testEval(EvalResult.FALSE, "-9734736690233", "-9734736690233", RelationSymbol.LESS, "-9734736690234");
	}
	
	// TODO test Geq und Greater

	private void testEval(final EvalResult expected, final String octIvlMin, final String octIvlMax,
			final RelationSymbol relSymb, final String fraction) {
		final OctInterval octIvl = new OctInterval(OctValue.parse(octIvlMin), OctValue.parse(octIvlMax));
		testEval(expected, octIvl, relSymb, parseFraction(fraction));
	}
	
	private Rational parseFraction(final String fraction) {
		final int fractionLine = fraction.indexOf('/');
		if (fractionLine < 0) {
			return Rational.valueOf(new BigInteger(fraction), BigInteger.ONE);
		} else {
			return Rational.valueOf(new BigInteger(fraction.substring(0, fractionLine)),
					new BigInteger(fraction.substring(fractionLine + 1)));
		}
	}

	private void testEval(final EvalResult expected, final OctInterval octIvl,
			final RelationSymbol relSymb, final Rational constant) {
		Assert.assertEquals(expected, octIvl.evaluate(relSymb, constant));
	}
}
