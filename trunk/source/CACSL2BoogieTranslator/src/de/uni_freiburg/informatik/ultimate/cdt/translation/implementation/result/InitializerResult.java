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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.Collections;
import java.util.List;

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
	private final ExpressionResult mRootExpressionResult;

	/**
	 * The RValue in mExpressionResult may have a designator. This field stores it.
	 * (Can happen only if we are inside a nested initializer.)
	 */
	private final String mRootDesignator;

	private final List<InitializerResult> mChildren;

	/**
	 *
	 * @param node just for handing through to super class, can be null
	 * @param expressionResult
	 * @param treeNodeIds
	 * @param treeNodeIdToRValue
	 * @param treeNodeIdToDesignatorName
	 */
	public InitializerResult(final BoogieASTNode node, final String rootDesignator,
			final ExpressionResult expressionResult, final List<InitializerResult> children) {
		super(node);
		mRootDesignator = rootDesignator;
		mRootExpressionResult = expressionResult;
		mChildren = children == null ? null : Collections.unmodifiableList(children);
	}

	public String getRootDesignator() {
		return mRootDesignator;
	}

	public ExpressionResult getRootExpressionResult() {
		return mRootExpressionResult;
	}

	public boolean isInitializerList() {
		return mChildren != null;
	}

	public List<InitializerResult> getList() {
		return mChildren;
	}

	public boolean hasRootDesignator() {
		return mRootDesignator != null;
	}

	public boolean hasRootExpressionResult() {
		return mRootExpressionResult != null;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (hasRootDesignator()) {
			sb.append(getRootDesignator());
			sb.append(" : ");
		}
		if (hasRootExpressionResult()) {
			sb.append(getRootExpressionResult().getLrValue().toString());
		}

		if (isInitializerList()) {
			String comma = "";
			sb.append("{ ");
			for (final InitializerResult entry : getList()) {
				sb.append(comma);
				comma = ", ";
				sb.append(entry.toString());
			}
			sb.append(" }");
		}
		return sb.toString();
	}

	public static ExpressionResult getFirstValueInInitializer(final InitializerResult ir) {
		if (ir.hasRootExpressionResult()) {
			return ir.getRootExpressionResult();
		}
		if (!ir.getList().isEmpty()) {
			return getFirstValueInInitializer(ir.getList().get(0));
		}
		throw new AssertionError("found no value in initializer");
	}
}
