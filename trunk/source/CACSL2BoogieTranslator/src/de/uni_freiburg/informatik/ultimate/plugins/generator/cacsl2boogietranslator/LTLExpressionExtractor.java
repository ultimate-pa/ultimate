package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.LTLPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLTransformer;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLVisitor;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;

/**
 * @author dietsch@informatik.uni-freiburg.de
 */
public class LTLExpressionExtractor {

	private String mLTLFormatString;
	private LinkedHashMap<String, Expression> mMap;

	// alphabet without X, U, F, G
	private static final String sAlpha = "ABCDEHIJKLMNOPQRSTVWYZ";

	/**
	 * @return true iff ACSLNode is a GlobalLTLInvariant and everything is done,
	 *         false otherwise
	 */
	public boolean run(ACSLNode node) {
		LTLPrettyPrinter printer = new LTLPrettyPrinter();
		mLTLFormatString = printer.print(node);

		mMap = null;
		node = node.accept(new LTLReplaceWeakUntil());
		LTLExtractSubexpressions visitor = new LTLExtractSubexpressions();
		node.accept(visitor);

		// consolidate expression list, replace format string
		if (visitor.getResult() != null) {
			LinkedHashMap<String, Expression> map = new LinkedHashMap<>();
			for (Expression current : visitor.getResult()) {
				map.put(printer.print(current), current);
			}

			mMap = new LinkedHashMap<>();

			int i = 0;
			for (Entry<String, Expression> current : map.entrySet()) {
				String symbol = getAPSymbol(i);
				mLTLFormatString = replaceAllExpressionsWithAP(mLTLFormatString, symbol, current.getKey());
				mMap.put(symbol, current.getValue());
				i++;
			}
			return true;
		}
		return false;
	}

	public Map<String, Expression> getAP2SubExpressionMap() {
		return mMap;
	}

	public String getLTLFormatString() {
		return mLTLFormatString;
	}

	public static String replaceAllExpressionsWithAP(String input, String ap, String subExpression) {
		String key = subExpression.replaceAll("\\(", "\\\\(").replaceAll("\\)", "\\\\)");
		return input.replaceAll(key, ap);
	}

	public static String getAPSymbol(int i) {
		if (i < sAlpha.length()) {
			return String.valueOf(sAlpha.charAt(i));
		}

		String rtr = "A";
		int idx = i;
		while (idx > sAlpha.length()) {
			idx = idx - sAlpha.length();
			rtr += String.valueOf(sAlpha.charAt(idx % sAlpha.length()));
		}
		return rtr;
	}

	private class LTLReplaceWeakUntil extends ACSLTransformer {

		@Override
		public BinaryExpression transform(BinaryExpression node) {

			if (node.getOperator().equals(Operator.LTLWEAKUNTIL)) {
				// a WU b == (a U b) || (G a)
				Expression left = node.getLeft().accept(this);
				Expression right = node.getRight().accept(this);

				BinaryExpression until = new BinaryExpression(Operator.LTLUNTIL, left, right);
				UnaryExpression globally = new UnaryExpression(UnaryExpression.Operator.LTLGLOBALLY, left);
				BinaryExpression or = new BinaryExpression(Operator.LOGICOR, until, globally);

				addAdditionalInfo(node, until);
				addAdditionalInfo(node, globally);
				addAdditionalInfo(node, or);

				return or;
			}

			return super.transform(node);
		}

		private void addAdditionalInfo(BinaryExpression node, Expression expr) {
			expr.setEndingLineNumber(node.getEndingLineNumber());
			expr.setStartingLineNumber(node.getStartingLineNumber());
			expr.setFileName(node.getFileName());
			expr.setType(node.getType());
		}

	}

	private class LTLExtractSubexpressions extends ACSLVisitor {

		private Expression mCurrentSubExpression;
		private List<Expression> mExpressions;

		private LTLExtractSubexpressions() {
			mCurrentSubExpression = null;
			mExpressions = new ArrayList<>();
		}

		public List<Expression> getResult() {
			return mExpressions;
		}

		@Override
		public boolean visit(BinaryExpression node) {
			switch (node.getOperator()) {
			case LTLUNTIL:
			case LTLWEAKUNTIL:
			case LTLRELEASE:
				mCurrentSubExpression = null;
				return super.visit(node);
			default:
				if (mCurrentSubExpression == null) {
					LTLExtractSubexpressions left = new LTLExtractSubexpressions();
					LTLExtractSubexpressions right = new LTLExtractSubexpressions();
					node.getLeft().accept(left);
					node.getRight().accept(right);

					if (left.getResult().isEmpty() && right.getResult().isEmpty()) {
						mCurrentSubExpression = node;
					} else if (left.getResult().size() == 1 && left.getResult().get(0) == node.getLeft()
							&& right.getResult().size() == 1 && node.getRight() == right.getResult().get(0)) {
						mCurrentSubExpression = node;
					}
				}
				return super.visit(node);
			}
		}

		@Override
		public boolean visit(UnaryExpression node) {
			switch (node.getOperator()) {
			case LTLFINALLY:
			case LTLGLOBALLY:
			case LTLNEXT:
				mCurrentSubExpression = null;
				break;
			default:
				if (mCurrentSubExpression == null) {
					mCurrentSubExpression = node;
				}
				break;
			}
			return super.visit(node);
		}

		@Override
		public boolean visit(BooleanLiteral node) {
			literalReached();
			return super.visit(node);
		}

		@Override
		public boolean visit(IdentifierExpression node) {
			literalReached();
			return super.visit(node);
		}

		@Override
		public boolean visit(IntegerLiteral node) {
			literalReached();
			return super.visit(node);
		}

		@Override
		public boolean visit(RealLiteral node) {
			literalReached();
			return super.visit(node);
		}

		private void literalReached() {
			if (mCurrentSubExpression != null && mExpressions != null) {
				mExpressions.add(mCurrentSubExpression);
				mCurrentSubExpression = null;
			}
		}
	}
}