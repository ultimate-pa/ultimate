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

/**
 * Represents the regular expressions which matches only the empty. The empty word is often denoted as the greek letter
 * ε (epsilon) or λ (lambda). In Tarjan's 1981 paper it is written as Λ (captial lambda).
 * <p>
 * Since there is only one empty word regex this class is a singleton.
 *
 * @param <L>
 *            Type of letters that are used inside regex literals
 */
public class Epsilon<L> implements IRegex<L> {

	@SuppressWarnings("rawtypes")
	public static final Epsilon INSTANCE = new Epsilon();

	/**
	 * Private constructor since this is a singleton. Use factory method {@link Regex#epsilon()} to access the
	 * singleton.
	 */
	private Epsilon() {
	}

	@Override
	public String toString() {
		return "ε";
	}

	@Override
	public <RET, ARG> RET accept(final IRegexVisitor<L, RET, ARG> visitor, final ARG argument) {
		return visitor.visit(this, argument);
	}
}
