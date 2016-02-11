package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.CollectionUtil;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class IfExpressionTree {

	public static IfExpressionTree buildTree(Expression e, ExpressionTransformer exprTransformer) {
		if (e instanceof IfThenElseExpression) {
			return treeFromIfExpr((IfThenElseExpression) e, exprTransformer);
		} else if (e instanceof BinaryExpression) {
			return treeFromBinaryExpr((BinaryExpression) e, exprTransformer);
		} else if (e instanceof UnaryExpression) {
			return treeFromUnaryExpr((UnaryExpression) e, exprTransformer);
		} else {
			// Expression does not contain further expressions
			// except for Quantifiers or Array*Expressions -- but they are are not interpreted by the post-operator
			return new IfExpressionTree(e);
		}
	}

	private static IfExpressionTree treeFromIfExpr(IfThenElseExpression e, ExpressionTransformer exprTransformer) {
		Expression thenCondition, elseCondition;
		thenCondition = e.getCondition();
		if (thenCondition instanceof WildcardExpression) {
			thenCondition = elseCondition = new BooleanLiteral(thenCondition.getLocation(), true);
		} else {
			// note: condition may contain further IfThenElseExpressions, which will not be removed.
			elseCondition = exprTransformer.logicNegCached(thenCondition);
		}
		return new IfExpressionTree(
				thenCondition, buildTree(e.getThenPart(), exprTransformer),
				elseCondition, buildTree(e.getElsePart(), exprTransformer));
	}

	private static IfExpressionTree treeFromBinaryExpr(BinaryExpression be, ExpressionTransformer exprTransformer) {
		IfExpressionTree leftTree = buildTree(be.getLeft(), exprTransformer);
		IfExpressionTree rightTree = buildTree(be.getRight(), exprTransformer);

		ILocation beLocation = be.getLocation();
		IType beType = be.getType();
		BinaryExpression.Operator beOperator = be.getOperator();

		leftTree.append(rightTree, (left, right) -> new BinaryExpression(beLocation, beType, beOperator, left, right));
		return leftTree;
	}
	
	private static IfExpressionTree treeFromUnaryExpr(UnaryExpression ue, ExpressionTransformer exprTransformer) {
		IfExpressionTree subTree = buildTree(ue.getExpr(), exprTransformer);

		ILocation ueLocation = ue.getLocation();
		IType ueType = ue.getType();
		UnaryExpression.Operator ueOperator = ue.getOperator();

		subTree.mapLeafExprs(leafExpr -> new UnaryExpression(ueLocation, ueType, ueOperator, leafExpr));
		return subTree;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	/**
	 * Content of either the {@code then} or {@code else} part of an IfThenElseExpression.
	 * Not null <=> this is a leaf. All other attributes are null <=> this is a leaf.
	 */
	private Expression mLeafExpr;

	private Expression mThenCondition;
	private IfExpressionTree mThenChild;
	private Expression mElseCondition;
	private IfExpressionTree mElseChild;
	
	public IfExpressionTree(Expression expressionWithoutIf) {
		mLeafExpr = expressionWithoutIf;
	}

	public IfExpressionTree(Expression thenCondition, Expression elseCondition) {
		mThenCondition = thenCondition;
		mElseCondition = elseCondition;
	}

	public IfExpressionTree(Expression thenCondition, IfExpressionTree thenChild,
			Expression elseCondition, IfExpressionTree elseChild) {
		super();
		this.mThenCondition = thenCondition;
		this.mThenChild = thenChild;
		this.mElseCondition = elseCondition;
		this.mElseChild = elseChild;
	}

	public IfExpressionTree deepCopy() {
		if (isLeaf()) {
			return new IfExpressionTree(mLeafExpr);
		} else {
			return new IfExpressionTree(mThenCondition, mThenChild.deepCopy(), mElseCondition, mElseChild.deepCopy());
		}
	}

	public boolean isLeaf() {
		// TODO assert that (mLeafExpr == null) != (everythingOther == null);
		return mLeafExpr != null;
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
	 * Appends a tree (called {@code suffix}) to each leaf of this tree. Leafs of this tree are replaced by the suffix,
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
		if (isLeaf()) {
			mThenCondition = suffix.mThenCondition;
			mElseCondition = suffix.mElseCondition;
			Function<Expression, Expression> curriedFunction = suffixLeaf -> function.apply(mLeafExpr, suffixLeaf);
			mThenChild = suffix.deepCopy();
			mThenChild.mapLeafExprs(curriedFunction);
			mElseChild = suffix; // may be modified
			mElseChild.mapLeafExprs(curriedFunction);
			mLeafExpr = null;
		} else {
			mThenChild.append(suffix, function);
			mElseChild.append(suffix, function);
		}
	}

//	private List<IfExpressionTree> leafs() {
//		List<IfExpressionTree> leafs;
//		if (isLeaf()) {
//			leafs = new ArrayList<>();
//			leafs.add(this);
//		} else {
//			leafs = mThenChild.leafs();
//			leafs.addAll(mElseChild.leafs());
//		}
//		return leafs;
//	}postOp
	
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

}
