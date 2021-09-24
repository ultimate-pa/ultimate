/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-srParse plug-in.
 *
 * The ULTIMATE Library-srParse plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-srParse plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-srParse plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-srParse plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-srParse plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * TODO: explain pattern
 *
 * @author Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class DeclarationPattern extends PatternType<DeclarationPattern> {

	private static final SrParseScopeGlobally INIT_SCOPE = new SrParseScopeGlobally();

	public enum VariableCategory {
		IN("Input"), OUT("Output"), HIDDEN("???"), CONST("CONST");

		private final String mKeyword;

		VariableCategory(final String keyword) {
			mKeyword = keyword;
		}

		public String getKeyword() {
			return mKeyword;
		}
	}

	private final String mType;
	private final VariableCategory mVisibility;
	private final Expression mExpression;

	public DeclarationPattern(final String ident, final String type, final VariableCategory visibility) {
		this(ident, type, visibility, null);
	}

	public DeclarationPattern(final String ident, final String type, final VariableCategory visibility,
			final Expression expr) {
		super(INIT_SCOPE, ident, Collections.emptyList(), Collections.emptyList(), Collections.emptyList());
		mType = type;
		mVisibility = visibility;
		mExpression = expr;
	}

	@Override
	public DeclarationPattern create(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		throw new UnsupportedOperationException();
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
		final String prefix = mVisibility.getKeyword() + " " + getId() + " IS ";
		if (mVisibility == VariableCategory.CONST) {
			return prefix + BoogiePrettyPrinter.print(getExpression());
		}
		return prefix + mType;
	}

	@Override
	protected List<CounterTrace> transform(final CDD[] cdds, final int[] durations) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mExpression == null ? 0 : mExpression.hashCode());
		result = prime * result + (mType == null ? 0 : mType.hashCode());
		result = prime * result + (mVisibility == null ? 0 : mVisibility.hashCode());
		result = prime * result + (getId() == null ? 0 : getId().hashCode());
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
		final DeclarationPattern other = (DeclarationPattern) obj;
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
	public DeclarationPattern rename(final String newName) {
		return new DeclarationPattern(newName, getType(), getCategory(), getExpression());
	}

	@Override
	public int getExpectedCddSize() {
		return 0;
	}

	@Override
	public int getExpectedDurationSize() {
		return 0;
	}
}
