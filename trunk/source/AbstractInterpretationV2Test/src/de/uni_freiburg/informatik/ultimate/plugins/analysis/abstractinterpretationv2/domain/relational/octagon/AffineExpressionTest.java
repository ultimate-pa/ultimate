package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.Assert;
import org.junit.Test;

public class AffineExpressionTest {

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
		AffineExpression a = ae("2x + y + 1w + -2");
		AffineExpression b = ae("-3x + 0.1z + -1w + 0.5");
		AffineExpression expected = ae("-1x + y + 0.1z + -1.5");
		Assert.assertEquals(expected, a.add(b));
	}
	
	@Test 
	public void testNegation() {
		AffineExpression a = ae("2x + -0.1y + -2");
		AffineExpression aNegated = ae("-2x + 0.1y + 2");
		Assert.assertEquals(aNegated, a.negate());
		Assert.assertEquals(a, aNegated.negate());
	}

	@Test
	public void testMultiplication() {
		Assert.assertEquals(ae("-82"), ae("-4.1").multiply(ae("0.002e4")));
		Assert.assertEquals(null, ae("x").multiply(ae("x")));
		Assert.assertEquals(null, ae("x").multiply(ae("y")));

		String a = "3x + 9y + 6";
		String b = "0.5";
		String expected = "1.5x + 4.5y + 3";
		Assert.assertEquals(ae(expected), ae(a).multiply(ae(b)));
		Assert.assertEquals(ae(expected), ae(b).multiply(ae(a)));
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

		assertDivReal("x", "x", "1");
		assertDivReal("x", "y", null);
		assertDivReal("x + 1", "x", null);
		assertDivReal("x", "x + 1", null);
		
		assertDivReal("2x + -4.4y + 3.00z + -100", "-4.40y + 3z + 2.000x + -1e2", "1");

		String a1 = "2x + -6y + 3.4";
		String a2 = "4x + -12y + 6.8";
		assertDivReal(a1, a2, "0.5");
		assertDivReal(a2, a1, "2");
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
		
		assertDivInt("x", "x", "1");
		assertDivInt("x", "y", null);
		assertDivInt("x + 1", "x", null);
		assertDivInt("x", "x + 1", null);

		assertDivInt("2x + -4y + 3z + -100", "-4y + 2x + 3z + -1e2", "1");

		String a1 = "2x + -6y + 3";
		String a2 = "4x + -12y + 6";
		assertDivInt(a1, a2, null); // real result = 0.5
		assertDivInt(a2, a1, "2");
		assertDivInt(a2, "2", a1);
	}

	@Test
	public void testMod() {
		assertMod("x", "x", "0");
		assertMod("0", "0", "0");
		// TODO
	}
	
	private void assertDivReal(String a, String b, String expected) {
		assertDiv(a, b, expected, false);
	}

	private void assertDivInt(String a, String b, String expected) {
		assertDiv(a, b, expected, true);
	}

	private void assertDiv(String a, String b, String expected, boolean integerDivison) {
		AffineExpression aExpr = ae(a);
		AffineExpression bExpr = ae(b);
		AffineExpression expectedExpr = ae(expected);
		AffineExpression actualExpr = aExpr.divide(bExpr, integerDivison);
		boolean equal = expectedExpr == null && actualExpr == null;
		equal = equal || (expectedExpr != null && expectedExpr.equals(actualExpr));
		if (!equal) {
			String msg = "\n(  " + aExpr + "  )  /  (  " + bExpr + "  )";
			msg += "\nexpected: " + expectedExpr;
			msg += "\nwas: " + actualExpr;
			Assert.fail(msg);
		}
	}

	private void assertMod(String a, String b, String rExpected) {
		Assert.assertEquals(ae(rExpected), ae(a).modulo(ae(b)));
	}
	
	// Variable names with 'e' or 'E' are not allowed
	private static AffineExpression ae(String expr) {
		if (expr == null) {
			return null;
		}
		Map<String, BigDecimal> coefficients = new HashMap<>();
		BigDecimal constant = BigDecimal.ZERO;

		expr = expr.replace(" ", "");
		Matcher m = sCoeffVarRegex.matcher(expr);
		while (m.find()) {
			String var = m.group(sVarGroup);
			String coeffStr = m.group(sNumGroup);
			BigDecimal coeff = (coeffStr == null) ? BigDecimal.ONE : new BigDecimal(coeffStr);
			BigDecimal old = coefficients.put(var, coeff);
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
	
	private static final String sNumGroup = "num";
	private static final String sVarGroup = "var";
	private static final String sNumRegex = "(?<" + sNumGroup + ">[-+]?[0-9]*\\.?[0-9]+([eE][-+]?[0-9]+)?)";
	private static final String sVarRegex = "(?<" + sVarGroup + ">[a-df-zA-DF-Z]+)";
	private static final Pattern sCoeffVarRegex = Pattern.compile("^(" + sNumRegex + "\\*?)?" + sVarRegex + "(\\+|$)");

}
