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

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.IRegex;

public abstract class Regex {

	public static <V> IRegex<V> union(IRegex<V> a, IRegex<V> b) {
		return new Union<>(a, b);
	}

	public static <V> IRegex<V> concat(IRegex<V> a, IRegex<V> b) {
		return new Concatenate<>(a, b);
	}

	public static <V> IRegex<V> star(IRegex<V> a) {
		return new Star<>(a);
	}

	public static <V> IRegex<V> literal(V lit) {
		return new Plain<>(lit);
	}

	@SuppressWarnings("unchecked")
	public static final <V> Epsilon<V> epsilon() {
		return (Epsilon<V>) Epsilon.INSTANCE;
	}

	@SuppressWarnings("unchecked")
	public static final <V> EmptySet<V> emptySet() {
		return (EmptySet<V>) EmptySet.INSTANCE;
	}

	public static <V> IRegex<V> simplifiedUnion(IRegex<V> a, IRegex<V> b) {
		if (a instanceof EmptySet)
			return b;
		if (b instanceof EmptySet)
			return a;
		// The following case is not part of Tarjan's simplification operator "[R]".
		// However, it does not seem to break anything and helps if a graph contains one label multiple times.
		if (a.equals(b))
			return a;
		return union(a, b);
	}

	public static <V> IRegex<V> simplifiedConcatenation(IRegex<V> a, IRegex<V> b) {
		if (a instanceof EmptySet || b instanceof EmptySet)
			return emptySet();
		if (a instanceof Epsilon)
			return b;
		if (b instanceof Epsilon)
			return a;
		return concat(a, b);
	}

	public static <V> IRegex<V> simplifiedStar(IRegex<V> reg) {
		if (reg instanceof EmptySet || reg instanceof Epsilon) {
			return epsilon();
		}
		return star(reg);
	}

}
