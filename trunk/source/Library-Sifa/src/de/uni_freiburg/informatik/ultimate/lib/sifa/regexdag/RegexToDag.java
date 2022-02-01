/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Concatenation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegexVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Union;

/**
 * Converts a regex into a regex dag.
 * A regex dag is a directed acyclic graph with exactly one source and one sink representing a regex.
 * Concatenation is represented by a linear sequence of nodes.
 * Union is represented by a fork/branch (and later by a join/merge).
 * Stars are treated like literals and are represented by a single node.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <L> Type of letters that are used inside regex literals
 */
public class RegexToDag<L> implements IRegexVisitor<L, RegexDagNode<L>, RegexDagNode<L>> {

	private RegexDag<L> mDag;

	public RegexToDag() {
		resetDag();
	}

	private final void resetDag() {
		mDag = new RegexDag<>(RegexDagNode.makeEpsilon(), RegexDagNode.makeEpsilon());
	}

	/**
	 * Incorporates a given regex into the current DAG.
	 * Use {@link #getDagAndReset()} to query the resulting DAG.
	 *
	 * @param regex Regex to be converted into a DAG
	 * @return Reference to the last RegexDagNode created for the given regex.<br>
	 *         For (a·b) this is a node containing the regex literal b.<br>
	 *         For (a∪b) this is a join node containing the regex ε.<br>
	 *         For (a)* this is a node containing the regex star (a)*.
	 */
	public RegexDagNode<L> add(final IRegex<L> regex) {
		// Warning: Works only when source and sink are epsilon.
		// If DAG was modified (for instance compressed) this approach will produce wrong DAGs or even cycles.
		// Therefore we always clear reset dag when giving a reference to the outside world.
		// Alternatively we could copy, but there so far there is no use case for add() getDag() add() getDagAndReset()
		final RegexDagNode<L> regexSink = regex.accept(this, mDag.getSource());
		regexSink.connectOutgoing(mDag.getSink());
		return regexSink;
	}

	/**
	 * Retrieves the DAG built from possibly multiple regexes and clears this object's intern state.
	 *
	 * @return The regex DAG built from all {@link #add(IRegex)} since the last {@link #resetDag()}.
	 */
	public RegexDag<L> getDagAndReset() {
		final RegexDag<L> result = mDag;
		resetDag();
		return result;
	}

	@Override
	public RegexDagNode<L> visit(final Union<L> union, final RegexDagNode<L> parent) {
		final RegexDagNode<L> join = RegexDagNode.makeEpsilon();
		join.connectIncoming(union.getFirst().accept(this, parent));
		join.connectIncoming(union.getSecond().accept(this, parent));
		return join;
	}

	@Override
	public RegexDagNode<L> visit(final Concatenation<L> concatenation, final RegexDagNode<L> parent) {
		return concatenation.getSecond().accept(this, concatenation.getFirst().accept(this, parent));
	}

	@Override
	public RegexDagNode<L> visit(final Star<L> star, final RegexDagNode<L> parent) {
		return appendAsNode(star, parent);
	}

	@Override
	public RegexDagNode<L> visit(final Literal<L> literal, final RegexDagNode<L> parent) {
		return appendAsNode(literal, parent);
	}

	@Override
	public RegexDagNode<L> visit(final Epsilon<L> epsilon, final RegexDagNode<L> parent) {
		// Appending ε to anything does not change anything ==> no need to actually append ε
		return parent;
	}

	@Override
	public RegexDagNode<L> visit(final EmptySet<L> emptySet, final RegexDagNode<L> parent) {
		// Could generate a smaller DAG, but empty set regex should never occur for SIFA anyways
		return appendAsNode(emptySet, parent);
	}

	private RegexDagNode<L> appendAsNode(final IRegex<L> regex, final RegexDagNode<L> parent) {
		final RegexDagNode<L> newSink = new RegexDagNode<>(regex);
		parent.connectOutgoing(newSink);
		return newSink;
	}
}
