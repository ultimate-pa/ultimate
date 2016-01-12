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
	public void testAdd() {
		AffineExpression a = ae("2x + y + 1w + -2");
		AffineExpression b = ae("-3x + 0.1z + -1w + 0.5");
		AffineExpression expected = ae("-1x + y + 0.1z + -1.5");
		Assert.assertEquals(expected, a.add(b));
	}
	
	@Test 
	public void testNegate() {
		AffineExpression a = ae("2x + -0.1y + -2");
		AffineExpression aNegated = ae("-2x + 0.1y + 2");
		Assert.assertEquals(aNegated, a.negate());
		Assert.assertEquals(a, aNegated.negate());
	}

	@Test 
	public void testDivision() {
		AffineExpression a = ae("6x + 0.4y + 2");
		AffineExpression b = ae("3.1");
		System.out.println(a.divide(b));
		// TODO write tests
	}
	
	private static AffineExpression ae(String expr) {
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
				throw new IllegalArgumentException("Multiple occurances of variable " + var);
			}
			expr = expr.substring(m.group().length()).replaceAll("^\\+", "");
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
	private static final String sVarRegex = "(?<" + sVarGroup + ">[a-zA-Z]+)";
	private static final Pattern sCoeffVarRegex = Pattern.compile("^(" + sNumRegex + "\\*?)?" + sVarRegex);

}
