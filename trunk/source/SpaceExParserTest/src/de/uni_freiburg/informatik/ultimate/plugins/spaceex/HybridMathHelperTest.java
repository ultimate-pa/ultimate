package de.uni_freiburg.informatik.ultimate.plugins.spaceex;

import static org.junit.Assert.assertEquals;

import java.util.List;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridMathHelper;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridMathHelper.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.SyntaxTree;

public class HybridMathHelperTest {
	
	@Test
	public void testExpressionToArray() {
		List<Operator> operators = HybridMathHelper.getAllAvailableOperators();
		String expression = "4 <= x <= 6 & 7 >= y >= 4";
		String[] res = HybridMathHelper.expressionToArray(operators, expression);
		String arrayString = "[";
		for (int i = 0; i < res.length; i++) {
			arrayString += res[i] + ", ";
		}
		arrayString += "]";
		assertEquals("[4, <=, x, <=, 6, &, 7, >=, y, >=, 4, ]", arrayString);
		SyntaxTree<String> tree = HybridMathHelper.arrayToTree(operators, res);
		System.out.println(tree.getRootNode().toString());
		HybridMathHelper.syntaxTreeToTerm(tree);
		// assertEquals("&<=10y<=76<=x4<=", prefixString);
	}
}
