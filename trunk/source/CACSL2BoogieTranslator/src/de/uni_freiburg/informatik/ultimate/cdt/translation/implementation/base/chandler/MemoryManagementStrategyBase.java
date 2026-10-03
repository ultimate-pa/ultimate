/*
 * Copyright (C) 2025 Jan Körner
 * Copyright (C) 2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Abstract base class for memory management strategies.
 *
 * This class implements the {@link IMemoryManagementStrategy} interface and provides common functionality for managing
 * memory, in particular by allocation and deallocation operations. Subclasses should extend this class to implement
 * specific memory management strategies.
 *
 * @author Jan Körner
 */
public abstract class MemoryManagementStrategyBase implements IMemoryManagementStrategy {
	protected final TypeSizes mTypeSizes;
	protected final ExpressionTranslation mExpressionTranslation;
	protected final ITypeHandler mTypeHandler;
	protected final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	protected boolean mAssumeAllocAlwaysSucceeds;

	public MemoryManagementStrategyBase(final TypeSizes typeSizes, final ExpressionTranslation expressionTranslation,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final boolean assumeAllocAlwaysSucceeds) {
		mTypeSizes = typeSizes;
		mExpressionTranslation = expressionTranslation;
		mTypeHandler = typeHandler;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mAssumeAllocAlwaysSucceeds = assumeAllocAlwaysSucceeds;
	}

	protected static Expression baseNotEqualZeroExpr(final ILocation tuLoc, final Expression resultExpr,
			final Expression zeroNumericValueExpr) {
		return ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPNEQ,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
				zeroNumericValueExpr);
	}

	protected Expression baseGreaterThanBarrier(final ILocation tuLoc, final Expression stackHeapBarrierExpr,
			final Expression resultExpr) {
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
				IASTBinaryExpression.op_greaterThan,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
				mExpressionTranslation.getCTypeOfPointerComponents(), stackHeapBarrierExpr,
				mExpressionTranslation.getCTypeOfPointerComponents());
	}

	protected Expression baseSmallerThanBarrier(final ILocation tuLoc, final Expression stackHeapBarrierExpr,
			final Expression resultExpr) {
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
				IASTBinaryExpression.op_lessThan,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
				mExpressionTranslation.getCTypeOfPointerComponents(), stackHeapBarrierExpr,
				mExpressionTranslation.getCTypeOfPointerComponents());
	}
}
