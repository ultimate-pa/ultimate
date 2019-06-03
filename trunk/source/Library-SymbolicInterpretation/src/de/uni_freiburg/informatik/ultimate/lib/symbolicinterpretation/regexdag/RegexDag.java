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

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.util.datastructures.GraphToTgf;

/**
 * A DAG with exactly one source and exactly one sink representing a set of regexes.
 * Source and sink can be the same node.
 *
 * @see RegexDagNode
 * 
 * @author schaetzc@tf.uni-freiburg.de
 * 
 * @param <L> Type of letters that are used inside regex literals
 */
public class RegexDag<L> {

	private RegexDagNode<L> mSource;
	private RegexDagNode<L> mSink;

	/** Creates a DAG representing the empty word ε. */
	public static <L> RegexDag<L> makeEpsilon() {
		return singleNodeDag(Regex.epsilon());
	}

	/** Creates a DAG representing the never matching regex ∅. */
	public static <L> RegexDag<L> makeEmptySet() {
		return singleNodeDag(Regex.emptySet());
	}

	/**
	 * Creates a DAG with a single node which acts as both, the source and the sink.
	 * @param sourceSinkLabel Label of the only node
	 * @return DAG with only one newly created node
	 */
	public static <L> RegexDag<L> singleNodeDag(final IRegex<L> sourceSinkLabel) {
		return new RegexDag<>(new RegexDagNode<>(sourceSinkLabel));
	}

	/** Creates a DAG with a single node which acts as both, the source and the sink. */
	public RegexDag(final RegexDagNode<L> sourceAndSink) {
		this(sourceAndSink, sourceAndSink);
	}

	/**
	 * Creates a DAG with a source node and a sink node.
	 * Does <b>not</b> automatically connect both nodes.
	 */
	public RegexDag(final RegexDagNode<L> source, final RegexDagNode<L> sink) {
		mSource = source;
		mSink = sink;
	}

	public RegexDagNode<L> getSource() {
		return mSource;
	}

	public RegexDagNode<L> getSink() {
		return mSink;
	}

	public void setSource(final RegexDagNode<L> source) {
		mSource = source;
	}

	public void setSink(final RegexDagNode<L> sink) {
		mSink = sink;
	}

	public String toString() {
		return new GraphToTgf<>(mSource).includeComponentOf(mSink).getTgf();
	}
}



