package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieUtil;

public class AffineExpressionTest {

	private Map<IBoogieType, Map<String, IBoogieVar>> mVarCache;

	@Before
	public void setup() {
		mVarCache = new HashMap<IBoogieType, Map<String, IBoogieVar>>();
		mVarCache.put(BoogieType.TYPE_INT, new HashMap<>());
		mVarCache.put(BoogieType.TYPE_REAL, new HashMap<>());
	}

	@Test
	public void testEquals() {
		Assert.assertEquals(ae("1.41"), ae("1.41"));
		Assert.assertEquals(ae("x + y"), ae("y + x"));
		Assert.assertEquals(ae("4x + 3.14y + -3"), ae("4x + 3.14y + -3"));
		Assert.assertEquals(ae("3x + 10.000"), ae("3.00x + 10.0"));
		Assert.assertEquals(ae("0x + y"), ae("y"));

		Assert.assertNotEquals(ae("x + y"), ae("x + y + 1"));
		Assert.assertNotEquals(ae("x + y"), ae("x + y + z"));
	}

	@Test
	public void testAddition() {
		final AffineExpression a = ae("2x + y + 1w + -2");
		final AffineExpression b = ae("-3x + 0.1z + -1w + 0.5");
		final AffineExpression expected = ae("-1x + y + 0.1z + -1.5");
		Assert.assertEquals(expected, a.add(b));
	}

	@Test
	public void testNegation() {
		final AffineExpression a = ae("2x + -0.1y + -2");
		final AffineExpression aNegated = ae("-2x + 0.1y + 2");
		Assert.assertEquals(aNegated, a.negate());
		Assert.assertEquals(a, aNegated.negate());
	}

	@Test
	public void testMultiplication() {
		Assert.assertEquals(ae("-82"), ae("-4.1").multiply(ae("0.002e4")));
		Assert.assertEquals(null, ae("x").multiply(ae("x")));
		Assert.assertEquals(null, ae("x").multiply(ae("y")));

		final String a = "3x + 9y + 6";
		final String b = "0.5";
		final String expected = "1.5x + 4.5y + 3.0";
		Assert.assertEquals(ae(expected).toString(), ae(a).multiply(ae(b)).toString());
		Assert.assertEquals(ae(expected).toString(), ae(b).multiply(ae(a)).toString());
	}

	@Test
	public void testDivisionReals() {
		assertDivReal("1", "0", null);
		assertDivReal("x", "0", null);

		assertDivReal("1", "+2", "+0.5");
		assertDivReal("+1", "-2", "-0.5");
		assertDivReal("-1", "+2", "-0.5");
		assertDivReal("-1", "-2", "+0.5");
		assertDivReal("-1", "-2", "+0.5");
		assertDivReal("1", "3", null);

		assertDivReal("x", "x", null);
		assertDivReal("x", "y", null);
		assertDivReal("x + 1", "x", null);
		assertDivReal("x", "x + 1", null);

		assertDivReal("2x + -4.4y + 3.00z + -100", "-4.40y + 3z + 2.000x + -1e2", null);

		final String a1 = "2x + -6y + 3.4";
		final String a2 = "4x + -12y + 6.8";
		assertDivReal(a1, a2, null);
		assertDivReal(a2, a1, null);
		assertDivReal(a1, "0.5", a2);
		assertDivReal(a2, "2", a1);
	}

	@Test
	public void testDivisionIntegers() {
		assertDivInt("1", "0", null);
		assertDivInt("x", "0", null);

		assertDivInt("+1", "+2", " 0");
		assertDivInt("+1", "-2", " 0");
		assertDivInt("-1", "+2", "-1");
		assertDivInt("-1", "-2", "+1");
		assertDivInt("1", "3", "0");

		assertDivInt("x", "x", null);
		assertDivInt("x", "y", null);
		assertDivInt("x + 1", "x", null);
		assertDivInt("x", "x + 1", null);

		assertDivInt("2x + -4y + 3z + -100", "-4y + 2x + 3z + -1e2", null);

		final String a1 = "2x + -6y + 3";
		final String a2 = "4x + -12y + 6";
		assertDivInt(a1, a2, null);
		assertDivInt(a2, a1, null);
		assertDivInt(a2, "2", a1);
	}

	@Test
	public void testMod() {
		assertMod(" 4", " 3", "1");
		assertMod(" 4", "-3", "1");
		assertMod("-4", " 3", "2");
		assertMod("-4", "-3", "2");

		assertMod("x", "y", null);
		assertMod("1", "x", null);
		assertMod("x", "1", null);

		assertMod("1", "0", null);
		assertMod("0", "0", null);
		assertMod("x", "x", null); // x could be 0
	}

	@Test
	public void testTwoVar() {
		AffineExpression.TwoVarForm tvf;

		tvf = ae("-1a + z + -1.5").getTwoVarForm();
		Assert.assertNotNull("TwoVarForm not recognized", tvf);
		Assert.assertEquals("a", tvf.var1.toString());
		Assert.assertEquals("z", tvf.var2.toString());
		Assert.assertEquals(true, tvf.negVar1);
		Assert.assertEquals(false, tvf.negVar2);
		Assert.assertTrue(tvf.constant.compareTo(OctValue.parse("-1.5")) == 0);

		tvf = ae("2y + 4").getTwoVarForm();
		Assert.assertNotNull("TwoVarForm not recognized", tvf);
		Assert.assertEquals("y", tvf.var1.toString());
		Assert.assertEquals("y", tvf.var2.toString());
		Assert.assertEquals(false, tvf.negVar1);
		Assert.assertEquals(false, tvf.negVar2);
		Assert.assertTrue(tvf.constant.compareTo(new OctValue(4)) == 0);

		Assert.assertNull(ae("-2.5x").getTwoVarForm());

		Assert.assertNull(ae("x + 2y").getTwoVarForm());
	}

	private void assertDivReal(String a, String b, String expected) {
		Assert.assertEquals(ae(expected), ae(a).divide(ae(b), false));
	}

	private void assertDivInt(String a, String b, String expected) {
		Assert.assertEquals(ae(expected), ae(a).divide(ae(b), true));
	}

	private void assertMod(String a, String b, String rExpected) {
		Assert.assertEquals(ae(rExpected), ae(a).modulo(ae(b)));
	}

	// Variable names with 'e' or 'E' are not allowed
	private AffineExpression ae(String expr) {
		if (expr == null) {
			return null;
		}
		final Map<IBoogieVar, BigDecimal> coefficients = new LinkedHashMap<>();
		BigDecimal constant = BigDecimal.ZERO;

		expr = expr.replace(" ", "");
		Matcher m = sCoeffVarRegex.matcher(expr);
		while (m.find()) {
			final String coeffStr = m.group(sNumGroup);
			final BigDecimal coeff = (coeffStr == null) ? BigDecimal.ONE : new BigDecimal(coeffStr);
			final IBoogieType type = isInteger(coeff) ? BoogieType.TYPE_INT : BoogieType.TYPE_REAL;
			final IBoogieVar var = getVar(m.group(sVarGroup), type);
			final BigDecimal old = coefficients.put(var, coeff);
			if (old != null) {
				throw new IllegalArgumentException("Variable occurred multiple times: " + var);
			}
			expr = expr.substring(m.group().length());
			m = sCoeffVarRegex.matcher(expr);
		}
		if (!expr.isEmpty()) {
			constant = new BigDecimal(expr);
		}
		return new AffineExpression(coefficients, constant);
	}

	private static boolean isInteger(final BigDecimal value) {
		if (value.scale() <= 0) {
			return true;
		}
		try {
			value.toBigIntegerExact();
			return true;
		} catch (ArithmeticException ex) {
			return false;
		}
	}

	private IBoogieVar getVar(final String name, final IBoogieType type) {
		final Map<String, IBoogieVar> cache = mVarCache.get(type);
		if (cache == null) {
			throw new UnsupportedOperationException("cache not available for type " + type);
		}
		final String iname = name.intern();
		final IBoogieVar rtr = cache.get(iname);
		if (rtr != null) {
			return rtr;
		}
		final IBoogieVar var = BoogieUtil.createTemporaryIBoogieVar(iname, type);
		cache.put(iname, var);
		return var;
	}

	private static final String sNumGroup = "num";
	private static final String sVarGroup = "var";
	private static final String sNumRegex = "(?<" + sNumGroup + ">[-+]?[0-9]*\\.?[0-9]+([eE][-+]?[0-9]+)?)";
	private static final String sVarRegex = "(?<" + sVarGroup + ">[a-df-zA-DF-Z]+)";
	private static final Pattern sCoeffVarRegex = Pattern.compile("^(" + sNumRegex + "\\*?)?" + sVarRegex + "(\\+|$)");

}
