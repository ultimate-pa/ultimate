package de.uni_freiburg.informatik.ultimate.plugins.spaceex;

import static org.junit.Assert.assertEquals;

import java.util.List;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridMathHelper;

public class HybridMathHelperTest {
	
	@Test
	public void testExpressionToArray() {
		final String expression = "4 <= x <= 6 & 7 >= y >= 4";
		final String[] infix = HybridMathHelper.expressionToArray(expression);
		String arrayString = "[";
		for (int i = 0; i < infix.length; i++) {
			arrayString += infix[i] + ", ";
		}
		arrayString += "]";
		assertEquals("[4, <=, x, <=, 6, &, 7, >=, y, >=, 4, ]", arrayString);
		final List<String> postfix = HybridMathHelper.postfix(infix);
	}
}
