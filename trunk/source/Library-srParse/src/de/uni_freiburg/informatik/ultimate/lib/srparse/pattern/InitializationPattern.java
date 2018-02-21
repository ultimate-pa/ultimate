package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;

/**
 *
 * @author Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 */
public class InitializationPattern extends PatternType {

	public enum VariableCategory {
		IN, OUT, HIDDEN, CONST
	}

	private final String mType;
	private final VariableCategory mVisibility;
	private final String mIdent;
	private final Expression mExpression;

	public InitializationPattern(final String ident, final String type, final VariableCategory visibility) {
		this(ident, type, visibility, null);
	}

	public InitializationPattern(final String ident, final String type, final VariableCategory visibility,
			final Expression expr) {
		mIdent = ident;
		mType = type;
		mVisibility = visibility;
		mExpression = expr;
	}

	public VariableCategory getCategory() {
		return mVisibility;
	}

	public String getIdent() {
		return mIdent;
	}

	public String getType() {
		return mType;
	}

	public Expression getExpression() {
		return mExpression;
	}

	@Override
	public String toString() {
		return mVisibility + " " + mIdent + " : " + mType;
	}
}
