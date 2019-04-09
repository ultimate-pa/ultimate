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

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Concatenation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegexVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Union;

public class RegexToDag<L> implements IRegexVisitor<L, RegexDagNode<L>, RegexDagNode<L>> {

	private RegexDag<L> mDag;
	private Set<Star<L>> mVisitedStars;
	private Queue<Star<L>> mStarWorklist;

	public RegexToDag() {
		resetDagAndStars();
	}

	public void resetDagAndStars() {
		resetDag();
		mVisitedStars = new HashSet<>();
		mStarWorklist = new ArrayDeque<>();
	}

	public void resetDag() {
		mDag = new RegexDag<>(RegexDagNode.makeEpsilon(), RegexDagNode.makeEpsilon());
	}

	/**
	 * Incorporates a given regex into the current DAG.
	 * 
	 * @param regex Regex to be converted into a DAG
	 * @return Reference to the resulting DAG. Referenced object may change in the future, see {@link #getDag()}.
	 */
	public RegexDag<L> apply(IRegex<L> regex) {
		final RegexDagNode<L> regexSink = regex.accept(this, mDag.getSource());
		// TODO mark regexSink or add it to a table? We need a way to distinguish errors and exits.
		regexSink.connectOutgoing(mDag.getSink());
		return mDag;
	}

	/**
	 * Retrieves the of star expressions treated like literals since the last {@link #resetDagAndStars()}.
	 * The list is free of duplicates. This returns a direct reference to the internal worklist;
	 * it is ok to modify the list from the outside, but running {@link #apply(IRegex)} may add something to the
	 * worklist.
	 * 
	 * @return Reference to the worklist of visited star expressions.
	 */
	public Queue<Star<L>> getStarWorklist() {
		return mStarWorklist;
	}

	/**
	 * Retrieves the DAG built from possibly multiple regexes.
	 * Caution: The retrieved DAG is only a reference and may change due to subsequent calls to {@link #apply(IRegex)}.
	 * Call {@link #resetDag()} to prevent this class from changing the retrieved DAG in the future.
	 * 
	 * @return The regex DAG built from all {@link #apply(IRegex)} since the last {@link #resetDag()}.
	 */
	public RegexDag<L> getDag() {
		return mDag;
	}

	@Override
	public RegexDagNode<L> visit(final Union<L> union, final RegexDagNode<L> parent) {
		final RegexDagNode<L> join = RegexDagNode.makeEpsilon();
		join.addIncoming(union.getFirst().accept(this, parent));
		join.addIncoming(union.getSecond().accept(this, parent));
		return join;
	}

	@Override
	public RegexDagNode<L> visit(final Concatenation<L> concatenation, final RegexDagNode<L> parent) {
		return concatenation.getSecond().accept(this, concatenation.getFirst().accept(this, parent));
	}

	@Override
	public RegexDagNode<L> visit(final Star<L> star, final RegexDagNode<L> parent) {
		if (mVisitedStars.add(star)) {
			mStarWorklist.add(star);
		}
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
