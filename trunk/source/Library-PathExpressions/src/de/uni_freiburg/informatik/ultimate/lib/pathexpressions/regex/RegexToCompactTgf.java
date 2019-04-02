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

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.RegexToCompactTgf.Arg;

/**
 * Converts a regex to a string in Trivial Graph Format (TGF) representing
 * a lossy compressed syntax tree of the regex.
 * <p>
 * <ul>
 * <li>Regex operations (star, union, ...) are nodes
 * <li>their operands (subexpressions) are their children
 * <li>Literals are leafs
 * <ul>
 * <p>
 * The only difference to {@link RegexToTgf} is the compression.
 * For better readability nested unions/concatenations are written as
 * one union/concatenation with more than two children.
 * The compression is lossy since the original parenthesization is lost.
 * In the compressed tree ((a·b)·c) and (a·(b·c)) look the same.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <L> Type of letters that are used inside regex literals
 */
public class RegexToCompactTgf<L> implements IRegexVisitor<L, RegexToCompactTgf<L>, Arg> {

	public static <L> String apply(final IRegex<L> regex) {
		return regex.accept(new RegexToCompactTgf<>()).toString();
	}
	
	protected static class Arg {
		public Arg(final int parentId, final IRegex<?> parent) {
			mParentId = parentId;
			mParentClass = parent.getClass();
		}
		protected final int mParentId;
		protected final Class<?> mParentClass;
		protected int mChildOffset;
	}

	protected int mNextNodeId;
	protected final StringBuilder mNodeList = new StringBuilder();
	protected final StringBuilder mEdgeList = new StringBuilder();

	protected int addNodeLinkedToParent(final String label, final Arg arg) {
		linkNextNodeToParent(arg);
		mNodeList.append(mNextNodeId).append(' ').append(label).append('\n');
		return mNextNodeId++;
	}

	protected void linkNextNodeToParent(final Arg arg) {
		if (arg == null) {
			return;
		}
		addEdge(arg.mParentId, mNextNodeId, arg.mChildOffset);
		++arg.mChildOffset;
	}

	protected void addEdge(final int sourceId, final int targetId, final int label) {
		mEdgeList.append(sourceId).append(' ').append(targetId).append(' ').append(label).append('\n');
	}

	private final RegexToCompactTgf<L> visitAndCompact(final String nodeLabel, final IRegex<L> node, Arg arg,
			final IRegex<L> leftChild, final IRegex<L> rightChild) {
		if (arg == null || node.getClass() != arg.mParentClass) {
			final int nodeId = addNodeLinkedToParent(nodeLabel, arg);
			arg = new Arg(nodeId, node);
		}
		leftChild.accept(this, arg);
		rightChild.accept(this, arg);
		return this;
	}
	
	@Override
	public RegexToCompactTgf<L> visit(final Union<L> union, Arg arg) {
		return visitAndCompact("∪", union, arg, union.getFirst(), union.getSecond());
	}

	@Override
	public RegexToCompactTgf<L> visit(final Concatenation<L> concatenation, Arg arg) {
		return visitAndCompact("·", concatenation, arg, concatenation.getFirst(), concatenation.getSecond());
	}

	@Override
	public RegexToCompactTgf<L> visit(final Star<L> star, Arg arg) {
		final int starId = addNodeLinkedToParent("*", arg);
		star.getInner().accept(this, new Arg(starId, star));
		return this;
	}

	@Override
	public RegexToCompactTgf<L> visit(final Literal<L> literal, final Arg arg) {
		addNodeLinkedToParent(literal.getLetter().toString(), arg);
		return this;
	}

	@Override
	public RegexToCompactTgf<L> visit(final Epsilon<L> epsilon, final Arg arg) {
		addNodeLinkedToParent("ε", arg);
		return this;
	}

	@Override
	public RegexToCompactTgf<L> visit(final EmptySet<L> emptySet, final Arg arg) {
		addNodeLinkedToParent("∅", arg);
		return this;
	}

	public String toString() {
		return mNodeList + "#\n" + mEdgeList;
	}

}
