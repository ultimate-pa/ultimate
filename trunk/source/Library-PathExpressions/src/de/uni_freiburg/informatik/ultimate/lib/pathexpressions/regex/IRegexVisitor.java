/*
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
 * Visitor for regular expression syntax trees.
 * <p>
 * In addition to the regular visitor pattern this visitor's method can take custom arguments
 * (in addition to syntax tree nodes) and return custom values.
 * <p>
 * The default implementation visits all syntax tree nodes using DFS from left to right,
 * passes custom arguments recursively, and returns null.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <L> Type of letters that are used inside regex literals
 * @param <RET> Custom return type, use Void if not needed
 * @param <ARG> Custom additional argument, use Void if not needed
 */
public interface IRegexVisitor<L, RET, ARG> {

	RET visit(final Union<L> union, final ARG argument);

	RET visit(final Concatenation<L> concatenation, final ARG argument);

	RET visit(final Star<L> star, final ARG argument);

	RET visit(final Literal<L> literal, final ARG argument);

	RET visit(final Epsilon<L> epsilon, final ARG argument);

	RET visit(final EmptySet<L> emptySet, final ARG argument);
}
