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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

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
	 * Indicates if this initializer has already been converted for a target type.
	 * Used for sanity checks.
	 */
	boolean mIsConvertedToTargetType;


	/**
	 * Stores all the code that is needed for evaluating the initializer.
	 *
	 * The values we store as RValues.
	 * So, if a switchToRValue introduced some Boogie code, it is saved in this top-level ExpressionResult.
	 * EDIT: because conversions work on ExpressionResults, we need to store ExpressionResults in the nodes (those can
	 *  can always hold RValues, though). We will need some flattening or so to get all Boogie code from all the nodes.
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

	/**
	 * We store this as a list to keep the ordering.
	 * Otherwise we could use mTreeNodeIdToValue.keySet() instead.
	 * (maybe we switch to a more elegant solution some time..)
	 */
	private final List<List<Integer>> mTreeNodeIds;

	private final Map<List<Integer>, ExpressionResult> mTreeNodeIdToValue;


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
			final List<List<Integer>> treeNodeIds, final Map<List<Integer>, ExpressionResult> treeNodeIdToRValue,
			final Map<List<Integer>, String> treeNodeIdToDesignatorName) {
		super(node);
		mExpressionResult = expressionResult;
		mTreeNodeIds = treeNodeIds;
		mTreeNodeIdToValue = treeNodeIdToRValue;
		mTreeNodeIdToDesignatorName = treeNodeIdToDesignatorName;
	}

	public Collection<List<Integer>> getTreeNodeIds() {
		assert assertNoDuplicateTreeNodeIds();
		return mTreeNodeIds;
	}

	public ExpressionResult getTreeNode(final List<Integer> nodeId) {
		return mTreeNodeIdToValue.get(nodeId);
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

	public boolean hasRootDesignator() {
		return mRootDesignator != null;
	}

	public InitializerResult rexBoolToIntIfNecessary(final ILocation loc, final AExpressionTranslation expressionTranslation) {
		mExpressionResult.rexBoolToIntIfNecessary(loc, expressionTranslation);

		for (final Entry<List<Integer>, ExpressionResult> en : new HashMap<>(mTreeNodeIdToValue).entrySet()) {
			en.getValue().rexBoolToIntIfNecessary(loc, expressionTranslation);
//			final RValue rVal = en.getValue();
//
//			if (rVal.isBoogieBool()) {
//				final RValue newRVal = RValue.boolToInt(loc, rVal, expressionTranslation);
//				mTreeNodeIdToValue.remove(en.getKey());
//				mTreeNodeIdToValue.put(en.getKey(), newRVal);
//			} else {
//				// do nothing
//			}
		}

		throw new AssertionError("TODO: immutable-stlye?..");
	}

	/**
	 * Should only happen when this is a non-aggregate initializer.
	 *
	 * @param loc
	 * @param main
	 * @param targetCType
	 */
	public InitializerResult convert(final ILocation loc, final Dispatcher main, final CType targetCType) {


		/*
		 * TODO: this conversion should also do the reordering due to designated intitializers (as the targetCType has
		 *  the information necessary for the reordering)
		 */

		if (targetCType instanceof CPrimitive || targetCType instanceof CEnum || targetCType instanceof CPointer) {
			assert mRootDesignator == null;
			assert mTreeNodeIds.isEmpty();

			main.mCHandler.convert(loc, mExpressionResult, targetCType);
			throw new AssertionError("TODO"); //TODO
		} else if (targetCType instanceof CStruct) {
			throw new AssertionError("TODO"); //TODO
		} else if (targetCType instanceof CArray) {
			throw new AssertionError("TODO"); //TODO
		} else {
			throw new UnsupportedOperationException("missing case?");
		}


		// TODO assert that all Boogie code from the ExpressionResults in the returned InitializerResult has been moved
		// to the root ExpressionResult.
	}

	private boolean assertNoDuplicateTreeNodeIds() {
		assert new HashSet<>(mTreeNodeIds).size() == mTreeNodeIds.size();
		return true;
	}

	public boolean hasBeenConvertedToTargetType() {
		return mIsConvertedToTargetType;
	}

	public boolean hasTreeNode(final List<Integer> arrayIndex) {
		return mTreeNodeIdToValue.containsKey(arrayIndex);
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
