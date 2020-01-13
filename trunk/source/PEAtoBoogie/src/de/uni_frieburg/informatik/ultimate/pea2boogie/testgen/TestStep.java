package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;

public class TestStep {

	final Map<IdentifierExpression, Collection<Expression>> mInputAssignment;
	final Map<IdentifierExpression, Collection<Expression>> mOutputAssignment;
	final Collection<Expression> mWaitTime;

	public TestStep(Map<IdentifierExpression, Collection<Expression>> inputAssignment,  Map<IdentifierExpression, Collection<Expression>> outputAssignment,
			Collection<Expression> delta) {
		mInputAssignment = inputAssignment;
		mOutputAssignment = outputAssignment;
		mWaitTime = delta;
	}

	@Override
	public String toString() {
		final StringBuilder result = new StringBuilder();

		result.append("\nSet Inputs:\n \t");
		for(final Entry<IdentifierExpression, Collection<Expression>> entry: mInputAssignment.entrySet()) {
			result.append(entry.getKey().getIdentifier());
			result.append(" := ");
			result.append(formatIdentToValue(entry.getValue()));
		}
		result.append("\n ");
		result.append("Wait at most ");
		result.append(formatIdentToValue(mWaitTime));
		result.append("for: \n\t");
		for(final Entry<IdentifierExpression, Collection<Expression>> entry: mOutputAssignment.entrySet()) {
			result.append(entry.getKey().getIdentifier());
			result.append(" == ");
			result.append(formatIdentToValue(entry.getValue()));
		}
		result.append("\n ");
		return result.toString();
	}

	private String formatIdentToValue(Collection<Expression> valueExpessions) {
		final StringBuilder result = new StringBuilder();
		for(final Expression expr: valueExpessions) {
			result.append(formatLiteral(expr));
		}
		result.append("  ");
		return result.toString();
	}

	private String formatLiteral(Expression expr) {
		if (expr instanceof BooleanLiteral) {
			return Boolean.toString(((BooleanLiteral) expr).getValue());
		} else if (expr instanceof IntegerLiteral) {
			return ((IntegerLiteral) expr).getValue();
		} else if (expr instanceof RealLiteral) {
			return ((RealLiteral) expr).getValue();
		}
		return "not antomic";
	}

}
