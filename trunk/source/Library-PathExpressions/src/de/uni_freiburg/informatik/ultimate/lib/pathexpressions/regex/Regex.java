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

public abstract class Regex {

	public static <L> IRegex<L> union(final IRegex<L> a, final IRegex<L> b) {
		return new Union<>(a, b);
	}

	public static <L> IRegex<L> concat(final IRegex<L> a, final IRegex<L> b) {
		return new Concatenation<>(a, b);
	}

	public static <L> IRegex<L> star(final IRegex<L> a) {
		return new Star<>(a);
	}

	public static <L> IRegex<L> literal(final L letter) {
		return new Literal<>(letter);
	}

	@SuppressWarnings("unchecked")
	public static final <L> Epsilon<L> epsilon() {
		return Epsilon.INSTANCE;
	}

	@SuppressWarnings("unchecked")
	public static final <L> EmptySet<L> emptySet() {
		return EmptySet.INSTANCE;
	}

	public static <L> IRegex<L> simplifiedUnion(final IRegex<L> a, final IRegex<L> b) {
		if (a instanceof EmptySet) {
			return b;
		} else if (b instanceof EmptySet) {
			return a;
		}
		// The following case is not part of Tarjan's simplification operator "[R]".
		// However, it does not seem to break anything and helps if a graph contains one label multiple times.
		if (a.equals(b)) {
			return a;
		}
		return union(a, b);
	}

	public static <L> IRegex<L> simplifiedConcatenation(final IRegex<L> a, final IRegex<L> b) {
		if (a instanceof EmptySet || b instanceof EmptySet) {
			return emptySet();
		} else if (a instanceof Epsilon) {
			return b;
		} else if (b instanceof Epsilon) {
			return a;
		}
		return concat(a, b);
	}

	public static <L> IRegex<L> simplifiedStar(final IRegex<L> reg) {
		if (reg instanceof EmptySet || reg instanceof Epsilon) {
			return epsilon();
		}
		return star(reg);
	}

}
