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
 * Converts a regex to a string in Trivial Graph Format (TGF) representing  the syntax tree of the regex.
 * <p>
 * <ul>
 * <li>Regex operations (star, union, ...) are nodes
 * <li>their operands (subexpressions) are their children
 * <li>Literals are leafs
 * <ul>
 * <p>
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <L> Type of letters that are used inside regex literals
 */
public class RegexToTgf<L> implements IRegexVisitor<L, RegexToTgf<L>, Void> {

	protected int mNextNodeId;
	protected final StringBuilder mNodeList = new StringBuilder();
	protected final StringBuilder mEdgeList = new StringBuilder();

	protected int addNode(final String label) {
		mNodeList.append(mNextNodeId).append(' ').append(label).append('\n');
		return mNextNodeId++;
	}

	protected void addLeftEdge(final int sourceId, final int targetId) {
		addEdge(sourceId, targetId, "0");
	}

	protected void addRightEdge(final int sourceId, final int targetId) {
		addEdge(sourceId, targetId, "1");
	}

	protected void addEdge(final int sourceId, final int targetId, final String label) {
		mEdgeList.append(sourceId).append(' ').append(targetId).append(' ').append(label).append('\n');
	}

	@Override
	public RegexToTgf<L> visit(final Union<L> union, final Void unused) {
		final int thisId = addNode("∪");
		addLeftEdge(thisId, mNextNodeId);
		union.getFirst().accept(this);
		addRightEdge(thisId, mNextNodeId);
		union.getSecond().accept(this);
		return this;
	}

	@Override
	public RegexToTgf<L> visit(final Concatenation<L> concatenation, final Void unused) {
		final int thisId = addNode("·");
		addLeftEdge(thisId, mNextNodeId);
		concatenation.getFirst().accept(this);
		addRightEdge(thisId, mNextNodeId);
		concatenation.getSecond().accept(this);
		return this;
	}

	@Override
	public RegexToTgf<L> visit(final Star<L> star, final Void unused) {
		final int thisId = addNode("*");
		addLeftEdge(thisId, mNextNodeId);
		star.getInner().accept(this);
		return this;
	}

	@Override
	public RegexToTgf<L> visit(final Literal<L> literal, final Void unused) {
		addNode(literal.getLetter().toString());
		return this;
	}

	@Override
	public RegexToTgf<L> visit(final Epsilon<L> epsilon, final Void unused) {
		addNode("ε");
		return this;
	}

	@Override
	public RegexToTgf<L> visit(final EmptySet<L> emptySet, final Void unused) {
		addNode("∅");
		return this;
	}

	public String toString() {
		return mNodeList + "#\n" + mEdgeList;
	}

}
