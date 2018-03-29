package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;

/**
 *
 * @author Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class InitializationPattern extends PatternType {

	public enum VariableCategory {
		IN, OUT, HIDDEN, CONST
	}

	private final String mType;
	private final VariableCategory mVisibility;
	private final Expression mExpression;

	public InitializationPattern(final String ident, final String type, final VariableCategory visibility) {
		this(ident, type, visibility, null);
	}

	public InitializationPattern(final String ident, final String type, final VariableCategory visibility,
			final Expression expr) {
		super(null, ident, null, null);
		mType = type;
		mVisibility = visibility;
		mExpression = expr;
	}

	public VariableCategory getCategory() {
		return mVisibility;
	}

	public String getType() {
		return mType;
	}

	public Expression getExpression() {
		return mExpression;
	}

	@Override
	public String toString() {
		return mVisibility + " " + getId() + " : " + mType;
	}

	@Override
	protected PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mExpression == null) ? 0 : mExpression.hashCode());
		result = prime * result + ((mType == null) ? 0 : mType.hashCode());
		result = prime * result + ((mVisibility == null) ? 0 : mVisibility.hashCode());
		result = prime * result + ((getId() == null) ? 0 : getId().hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!super.equals(obj)) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final InitializationPattern other = (InitializationPattern) obj;
		if (mVisibility != other.mVisibility) {
			return false;
		}

		if (mType == null) {
			if (other.mType != null) {
				return false;
			}
		} else if (!mType.equals(other.mType)) {
			return false;
		}

		if (getId() == null) {
			if (other.getId() != null) {
				return false;
			}
		} else if (!getId().equals(other.getId())) {
			return false;
		}

		if (mExpression == null) {
			if (other.mExpression != null) {
				return false;
			}
		} else if (!mExpression.equals(other.mExpression)) {
			return false;
		}

		return true;
	}

	@Override
	public PatternType rename(final String newName) {
		return new InitializationPattern(newName, getType(), getCategory(), getExpression());
	}
}
