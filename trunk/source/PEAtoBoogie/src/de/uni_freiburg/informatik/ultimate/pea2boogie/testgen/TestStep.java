package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;

public class TestStep {

	final Map<IdentifierExpression, Collection<Expression>> mInputAssignment;
	final Map<IdentifierExpression, Collection<Expression>> mOutputAssignment;
	final Map<IdentifierExpression, Collection<Expression>> mWaitForAssignment;
	final Collection<Expression> mWaitTime;

	public TestStep(final Map<IdentifierExpression, Collection<Expression>> inputAssignment,
			final Map<IdentifierExpression, Collection<Expression>> outputAssignment,
			final Map<IdentifierExpression, Collection<Expression>> waitForAssignment,
			final Collection<Expression> delta) {
		mInputAssignment = inputAssignment;
		mOutputAssignment = outputAssignment;
		mWaitForAssignment = waitForAssignment;
		mWaitTime = delta;
	}

	public Map<IdentifierExpression, Collection<Expression>> getInputAssignment() {
		return Collections.unmodifiableMap(mInputAssignment);
	}

	public Map<IdentifierExpression, Collection<Expression>> getOutputAssignment() {
		return Collections.unmodifiableMap(mOutputAssignment);
	}
	
	public Map<IdentifierExpression, Collection<Expression>> getWaitForAssignment() {
		return Collections.unmodifiableMap(mWaitForAssignment);
	}

	public Collection<Expression> getWaitTime() {
		return Collections.unmodifiableCollection(mWaitTime);
	}

	public boolean hasOutput() {
		return !mOutputAssignment.isEmpty();
	}

	public Set<String> getIdentifier() {
		final Set<String> result = new HashSet<>();
		mInputAssignment.keySet().forEach(e -> result.add(e.getIdentifier()));
		mOutputAssignment.keySet().forEach(e -> result.add(e.getIdentifier()));
		mWaitForAssignment.keySet().forEach(e -> result.add(e.getIdentifier()));

		return result;
	}

	@Override
	public String toString() {
		final StringBuilder result = new StringBuilder();

		result.append("\nSet Inputs:\n");
		for (final Entry<IdentifierExpression, Collection<Expression>> entry : mInputAssignment.entrySet()) {
			result.append("\t");
			result.append(entry.getKey().getIdentifier());
			result.append(" := ");
			result.append(formatIdentToValue(entry.getValue()));
			result.append("\n");
		}
		if (mOutputAssignment.size() > 0) {
			result.append("Observe: \n");
			for (final Entry<IdentifierExpression, Collection<Expression>> entry : mOutputAssignment.entrySet()) {
				result.append("\t");
				result.append(entry.getKey().getIdentifier());
				result.append(" == ");
				result.append(formatIdentToValue(entry.getValue()));
				result.append("\n");
			}
		}
		if (mWaitForAssignment.size() > 0) {
			result.append("Wait " + formatIdentToValue(mWaitTime) + "for output:\n");
			for (final Entry<IdentifierExpression, Collection<Expression>> entry : mWaitForAssignment.entrySet()) {
				result.append("\t");
				result.append(entry.getKey().getIdentifier());
				result.append(" == ");
				result.append(formatIdentToValue(entry.getValue()));
				result.append("\n");
			}
		} else {
			result.append("For the following " + formatIdentToValue(mWaitTime) + "time Units");
			result.append("\n");
		}

		result.append("\n ");
		return result.toString();
	}

	private static String formatIdentToValue(final Collection<Expression> valueExpessions) {
		final StringBuilder result = new StringBuilder();
		for (final Expression expr : valueExpessions) {
			result.append(formatLiteral(expr));
		}
		result.append("  ");
		return result.toString();
	}

	private static String formatLiteral(final Expression expr) {
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
