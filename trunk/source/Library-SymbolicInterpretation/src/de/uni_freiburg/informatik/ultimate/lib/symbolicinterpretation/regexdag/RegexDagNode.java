/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableDirectedGraph;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;

/**
 * Node of a {@link RegexDag}.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <L> Type of letters that are used inside regex literals
 */
public class RegexDagNode<L> extends ModifiableDirectedGraph<RegexDagNode<L>> {

	private static final long serialVersionUID = 1L;

	/**
	 * Content of this node, usually a regex which is either a literal, epsilon, empty set,
	 * or a regex whose outermost operator is a star.
	 * Concatenation and union can be represented by the DAG.
	 */
	private final IRegex<L> mContent;

	/**
	 * Create a DAG node whose content is the empty word ε.
	 * ε-nodes are often used as forks and joins since ε is the neutral argument of concatenation.
	 */
	public static <L> RegexDagNode<L> makeEpsilon() {
		return new RegexDagNode<>(Regex.epsilon());
	}

	public RegexDagNode(final IRegex<L> content) {
		mContent = content;
	}

	public boolean isEpsilon() {
		return mContent instanceof Epsilon<?>;
	}

	public IRegex<L> getContent() {
		return mContent;
	}

	@Override
	public String toString() {
		return mContent.toString();
	}
}
