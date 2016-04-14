/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.CollectionUtil;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * Represents an {@link Expression} as a set of if-free expression.
 * <p>
 * This representation is similar to the prenex normal form for quantifiers.
 * {@link IfThenElseExpression} are lifted to the top and build a binary tree,
 * where the edges are labeled with the assumed conditions from the {@linkplain IfThenElseExpression}s.
 * The leafs of the tree are if-free expressions.
 * <p>
 * Example: {@code x + (if c then y else z)} becomes {@code (if c then x + y else x + z)}, which is represented as
 * <pre>
 *      .
 *   c / \ !c
 *    /   \
 *  x+y   x+z
 * </pre>
 * <p>
 * Conditions, arrays, and quantifiers are not processed and may contain further {@linkplain IfThenElseExpression}s.
 * <p>
 * Trees are immutable after creation.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class IfExpressionTree {

	/**
	 * Construct a new {@linkplain IfExpressionTree} from an expression.
	 * @param expr Expression to be transformed.
	 * @param exprTransformer Transformer to be used for transformation (contains cache for negations of expressions).
	 * @return {@linkplain IfExpressionTree}
	 */
	public static IfExpressionTree buildTree(final Expression expr, final ExpressionTransformer exprTransformer) {
		if (expr instanceof IfThenElseExpression) {
			return treeFromIfExpr((IfThenElseExpression) expr, exprTransformer);
		} else if (expr instanceof BinaryExpression) {
			return treeFromBinaryExpr((BinaryExpression) expr, exprTransformer);
		} else if (expr instanceof UnaryExpression) {
			return treeFromUnaryExpr((UnaryExpression) expr, exprTransformer);
		} else {
			// Expression does not contain further expressions
			// except for quantifiers or arrays -- but they are are not interpreted by the post-operator
			return new IfExpressionTree(expr);
		}
	}

	/** @see #buildTree(Expression, ExpressionTransformer) */
	private static IfExpressionTree treeFromIfExpr(
			final IfThenElseExpression expr, final  ExpressionTransformer exprTransformer) {
		final Expression elseCondition;
		Expression thenCondition = expr.getCondition();
		if (thenCondition instanceof WildcardExpression) {
			thenCondition = elseCondition = new BooleanLiteral(thenCondition.getLocation(), BoogieType.boolType, true);
		} else {
			// note: condition may contain further IfThenElseExpressions, which will not be removed.
			elseCondition = exprTransformer.logicNegCached(thenCondition);
		}
		return new IfExpressionTree(
				thenCondition, buildTree(expr.getThenPart(), exprTransformer),
				elseCondition, buildTree(expr.getElsePart(), exprTransformer));
	}

	/** @see #buildTree(Expression, ExpressionTransformer) */
	private static IfExpressionTree treeFromBinaryExpr(
			final BinaryExpression binExpr, final ExpressionTransformer exprTransformer) {
		final IfExpressionTree leftTree = buildTree(binExpr.getLeft(), exprTransformer);
		final IfExpressionTree rightTree = buildTree(binExpr.getRight(), exprTransformer);

		final ILocation location = binExpr.getLocation();
		IType type = binExpr.getType();
		BinaryExpression.Operator operator = binExpr.getOperator();

		leftTree.append(rightTree, (left, right) -> new BinaryExpression(location, type, operator, left, right));
		return leftTree;
	}

	/** @see #buildTree(Expression, ExpressionTransformer) */
	private static IfExpressionTree treeFromUnaryExpr(
			final UnaryExpression unExpr, final ExpressionTransformer exprTransformer) {
		final IfExpressionTree subTree = buildTree(unExpr.getExpr(), exprTransformer);

		final ILocation location = unExpr.getLocation();
		final IType type = unExpr.getType();
		final UnaryExpression.Operator operator = unExpr.getOperator();

		subTree.mapLeafExprs(leafExpr -> new UnaryExpression(location, type, operator, leafExpr));
		return subTree;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	/**
	 * IfThenElseExpression-free content of either the {@code then} or {@code else} part of an IfThenElseExpression.
	 * Not null <=> this is a leaf. All other attributes are null <=> this is a leaf.
	 */
	private Expression mLeafExpr;

	/** Expression which needs to be assumed, when taking the then-branch. */
	private Expression mThenCondition;
	/** Branch corresponding to the then-part of the if. */
	private IfExpressionTree mThenChild;
	/** Expression which needs to be assumed, when taking the else-branch. */
	private Expression mElseCondition;
	/** Branch corresponding  to the else-part of the if. */
	private IfExpressionTree mElseChild;

	/**
	 * Create a new leaf of an IfExpressionTree.
	 * @param expressionWithoutIf Effective, if-free expression, when assuming all expressions on the path to this leaf.
	 */
	private IfExpressionTree(Expression expressionWithoutIf) {
		mLeafExpr = expressionWithoutIf;
	}

	/**
	 * Construct a new root node or internal node of an IfExpressionTree.
	 * The constructed node represents an {@link IfThenElseExpression}.
	 * 
	 * @param thenCondition Condition of the if.
	 * @param thenChild IfExpressionTree node when taking the then-branch.
	 * @param elseCondition Negated condition of the if.
	 * @param elseChild IfExpressionTree node when taking the else-branch.
	 */
	private IfExpressionTree(Expression thenCondition, IfExpressionTree thenChild,
			Expression elseCondition, IfExpressionTree elseChild) {
		if (thenCondition != null && thenCondition == thenChild.mThenCondition) {
			assert false;
		}
		mThenCondition = thenCondition;
		mThenChild = thenChild;
		mElseCondition = elseCondition;
		mElseChild = elseChild;
	}

	/**
	 * Deep-copy this tree. Only this node and its children is copied. Expressions are immutable and are not copied.
	 * @return Deep copy of this tree and its children
	 */
	public IfExpressionTree deepCopy() {
		if (isLeaf()) {
			return new IfExpressionTree(mLeafExpr);
		} else {
			return new IfExpressionTree(mThenCondition, mThenChild.deepCopy(), mElseCondition, mElseChild.deepCopy());
		}
	}

	/** @return This node is a leaf. */
	public boolean isLeaf() {
		assert compareNonLeafAttributesToNull(mLeafExpr == null);
		return mLeafExpr != null;
	}

	private boolean compareNonLeafAttributesToNull(boolean not) {
		return (not ^ (mThenCondition == null)) && (not ^ (mThenChild == null))
				&& (not ^ (mElseCondition == null)) && (not ^ (mElseChild == null));
	}

	private void mapLeafExprs(Function<Expression, Expression> function) {
		if (isLeaf()) {
			mLeafExpr = function.apply(mLeafExpr);
		} else {
			mThenChild.mapLeafExprs(function);
			mElseChild.mapLeafExprs(function);
		}
	}

	/**
	 * Appends a tree (called suffix) to each leaf of this tree. Leafs of this tree are replaced by the suffix,
	 * and the leafs of the suffix are replaced by the result of a function, which uses both old leafs as arguments.
	 * <p>
	 * Example: The input ...
	 * <pre>
	 * this       suffix    function
	 * -------    ------    ------------
	 *  (A)         (X)     f(t,s) = t.s
	 *  / \         / \
	 * b  (C)      y   z
	 *    / \
	 *   d   e
	 * </pre>
	 * ... results in the following tree
	 * <pre>
	 *       ____(A)____
	 *      /           \
	 *    (X)         ___(C)___
	 *   /   \       /         \
	 * b.y   b.z   (X)        (X)
	 *            /   \      /   \
	 *          d.y   d.z  e.y   e.z
	 * </pre>
	 *
	 * @param suffix tree to be appended (may be modified)
	 * @param function f(thisLeaf, suffixLeaf) = resultLeaf
	 */
	private void append(IfExpressionTree suffix, BiFunction<Expression, Expression, Expression> function) {
		if (suffix.isLeaf()) {
			// it is faster to handle this common case separately
			mapLeafExprs(thisLeaf -> function.apply(thisLeaf, suffix.mLeafExpr));
		} else {
			appendNonLeaf(suffix, function);
		}
	}

	private void appendNonLeaf(IfExpressionTree suffix, BiFunction<Expression, Expression, Expression> function) {
		if (isLeaf()) {
			assert !suffix.isLeaf();
			mThenCondition = suffix.mThenCondition;
			mElseCondition = suffix.mElseCondition;
			Function<Expression, Expression> curriedFunction = suffixLeaf -> function.apply(mLeafExpr, suffixLeaf);
			mThenChild = suffix.mThenChild.deepCopy();
			mThenChild.mapLeafExprs(curriedFunction);
			mElseChild = suffix.mElseChild.deepCopy();
			mElseChild.mapLeafExprs(curriedFunction);
			mLeafExpr = null;
		} else {
			mThenChild.appendNonLeaf(suffix, function);
			mElseChild.appendNonLeaf(suffix, function);
		}
	}

	public List<Pair<Expression, List<OctDomainState>>> assumeLeafs(OctPostOperator postOp,
			List<OctDomainState> oldStates) {

		if (isLeaf()) {
			return CollectionUtil.singeltonArrayList(new Pair<>(mLeafExpr, oldStates));
		}

		List<OctDomainState> thenStates, elseStates;

		int maxParallelStates = postOp.getMaxParallelStates();
		OctAssumeProcessor ap = postOp.getAssumeProcessor();
		thenStates = ap.assume(mThenCondition, OctPostOperator.deepCopy(oldStates));
		elseStates = ap.assume(mElseCondition, oldStates); // oldStates may be modified

		if (thenStates.size() + elseStates.size() > maxParallelStates) {
			// maybe we don't have to join if bottom states are removed
			thenStates = OctPostOperator.removeBottomStates(thenStates);
			elseStates = OctPostOperator.removeBottomStates(elseStates);
		}
		if (thenStates.size() + elseStates.size() > maxParallelStates) {
			thenStates = OctPostOperator.joinToSingleton(thenStates);
			elseStates = OctPostOperator.joinToSingleton(elseStates);
		}
		if (thenStates.size() + elseStates.size() > maxParallelStates) {
			// maxParallelStates == 1
			thenStates.addAll(elseStates);
			thenStates = OctPostOperator.joinToSingleton(thenStates);
			elseStates = OctPostOperator.deepCopy(thenStates);
		}

		List<Pair<Expression, List<OctDomainState>>> thenLeafs, elseLeafs;
		thenLeafs = mThenChild.assumeLeafs(postOp, thenStates);
		elseLeafs = mElseChild.assumeLeafs(postOp, elseStates);

		thenLeafs.addAll(elseLeafs);
		return thenLeafs;
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		toString("", sb);
		return sb.toString();
	}

    private void toString(String prefix, StringBuilder sb) {
    	if (isLeaf()) {
        	sb.append(prefix + "└╼ " + BoogiePrettyPrinter.print(mLeafExpr) + "\n");
        } else {
        	sb.append(prefix + "├─ " + BoogiePrettyPrinter.print(mThenCondition) + "\n");
        	mThenChild.toString(prefix + "│  ", sb);
        	sb.append(prefix + "└─ " + BoogiePrettyPrinter.print(mElseCondition) + "\n");
        	mElseChild.toString(prefix + "   ", sb);
        }
    }
}
