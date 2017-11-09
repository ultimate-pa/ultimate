/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Result for initializer lists. E.g. for arrays and structs.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;

/**
 * A Result for the C to Boogie translation.
 * Stores the result of translating an initializer.
 * An initializer essentially is a nested structure of ExpressionResults.
 *
 * As a special case an initializer may contain only one ExpressionResult, for example for initializing simple type
 * variables, like ints.
 *
 * This may also represent the translation of a struct initializer or of an initializer for a (multidimensional)
 * array.
 *
 * This implementation tries to follow section 6.7.9 of the C11 standard.
 *
 * @author Markus Lindenmann
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class InitializerResult extends Result {

	/**
	 * Stores all the code that is needed for evaluating the initializer.
	 * The values we store as RValues.
	 * So, if a switchToRValue introduced some Boogie code, it is saved in this top-level ExpressionResult.
	 *
	 * The RValue at the root of the tree is the RValue of this ExpressionResult.
	 *
	 * (We can/could also use this class for
	 *  initializers of non-aggregate type)
	 */
	private final ExpressionResult mExpressionResult;

	/**
	 * The RValue in mExpressionResult may have a designator. This field stores it.
	 * (Can happen only if we are inside a nested initializer.)
	 */
	private String mRootDesignator;

	private final List<List<Integer>> mTreeNodeIds;

	private final Map<List<Integer>, RValue> mTreeNodeIdToRValue;


	/**
	 * It is possible to give a struct initializer that lists the fields out of order by giving designators for each
	 * initialization value.
	 */
	private final Map<List<Integer>, String> mTreeNodeIdToDesignatorName;


	/**
	 *
	 * @param node just for handing through to super class, can be null
	 * @param expressionResult
	 * @param treeNodeIds
	 * @param treeNodeIdToRValue
	 * @param treeNodeIdToDesignatorName
	 */
	InitializerResult(final BoogieASTNode node, final ExpressionResult expressionResult,
			final List<List<Integer>> treeNodeIds, final Map<List<Integer>, RValue> treeNodeIdToRValue,
			final Map<List<Integer>, String> treeNodeIdToDesignatorName) {
		super(node);
		mExpressionResult = expressionResult;
		mTreeNodeIds = treeNodeIds;
		mTreeNodeIdToRValue = treeNodeIdToRValue;
		mTreeNodeIdToDesignatorName = treeNodeIdToDesignatorName;
	}

	public Collection<List<Integer>> getTreeNodeIds() {
		assert assertNoDuplicateTreeNodeIds();
		return mTreeNodeIds;
	}

	public RValue getTreeNode(final List<Integer> nodeId) {
		return mTreeNodeIdToRValue.get(nodeId);
	}

	public ExpressionResult getExpressionResult() {
		return mExpressionResult;
	}

	/**
	 * Return the direct children of this node
	 * @return
	 */
	public List<InitializerResult> getTopLevelChildren() {
		// TODO Auto-generated method stub
		return null;
	}

	private boolean assertNoDuplicateTreeNodeIds() {
		assert new HashSet<>(mTreeNodeIds).size() == mTreeNodeIds.size();
		return true;
	}

	public boolean hasRootDesignator() {
		return mRootDesignator != null;
	}

//	public LRValue getLrVal() {
//		return mExpressionResult.getLrValue();
//	}
//
//	public Collection<? extends Declaration> getDeclarations() {
//		return mExpressionResult.getDeclarations();
//	}
//
//	public Collection<? extends Statement> getStatements() {
//		return mExpressionResult.getStatements();
//	}
//
//	public Map<? extends VariableDeclaration, ? extends ILocation> getAuxVars() {
//		return mExpressionResult.getAuxVars();
//	}
//
//	public Collection<? extends Overapprox> getOverapprs() {
//		// TODO Auto-generated method stub
//		return null;
//	}

//	public Map<List<Integer>, ExpressionResult> getTree

//	public List<List<Integer>, ExpressionResult> get
}
