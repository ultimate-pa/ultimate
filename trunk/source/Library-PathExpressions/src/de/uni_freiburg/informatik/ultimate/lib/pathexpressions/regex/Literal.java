/*
 * Code taken from https://github.com/johspaeth/PathExpression
 * Copyright (C) 2018 Johannes Spaeth
 * Copyright (C) 2018 Fraunhofer IEM, Paderborn, Germany
 *
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-PathExpressions plug-in.
 *
 * The ULTIMATE Library-PathExpressions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-PathExpressions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-PathExpressions plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-PathExpressions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-PathExpressions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex;

import java.util.Objects;

/**
 * Represents the regular expressions which matches only a single letter.
 *
 * @param <L>
 *            Type of letters that are used inside regex literals
 */
public class Literal<L> implements IRegex<L> {
	private final L mLetter;

	/**
	 * Use factory method {@link Regex#literal(IRegex)} to create objects of this class.
	 */
	protected Literal(final L letter) {
		this.mLetter = letter;
	}

	public L getLetter() {
		return mLetter;
	}

	@Override
	public String toString() {
//		return "";
		return Objects.toString(mLetter);
	}

	@Override
	public int hashCode() {
		return mLetter == null ? 0 : mLetter.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (getClass() != obj.getClass()) {
			return false;
		}
		final Literal<?> other = (Literal<?>) obj;
		return Objects.equals(mLetter, other.mLetter);
	}

	@Override
	public <RET, ARG> RET accept(final IRegexVisitor<L, RET, ARG> visitor, final ARG argument) {
		return visitor.visit(this, argument);
	}
}