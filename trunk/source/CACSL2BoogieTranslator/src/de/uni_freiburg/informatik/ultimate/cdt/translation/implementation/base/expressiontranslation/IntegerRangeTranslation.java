/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Integer translation that uses the range-based approach. This means every expression is in the range of the
 * corresponding C-expression. To ensure this we need to insert modulos around every statement that can possibly lead to
 * a wraparound.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class IntegerRangeTranslation extends IntegerTranslation {
	public IntegerRangeTranslation(final TypeSizes typeSizeConstants, final TranslationSettings settings,
			final ITypeHandler typeHandler, final FlatSymbolTable symboltable) {
		super(typeSizeConstants, settings, typeHandler, symboltable);
	}

	@Override
	public Expression applyNutzWraparound(final ILocation loc, final CPrimitive cPrimitive, final Expression operand) {
		// No need to apply modulos here, since we used the range based translation
		return operand;
	}

	@Override
	protected Expression constructUnaryMinusExpression(final ILocation loc, final Expression expr,
			final CPrimitive type) {
		// For unsigneds we construct MAX_VALUE+1 - expr instead of -expr to remain in the range
		if (type.getGeneralType() == CPrimitiveCategory.INTTYPE && mTypeSizes.isUnsigned(type)) {
			final Expression maxValueMinusOne = constructLiteralForIntegerType(loc, type,
					mTypeSizes.getMaxValueOfPrimitiveType(type).subtract(BigInteger.ONE));
			return ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS, maxValueMinusOne, expr);
		}
		return super.constructUnaryMinusExpression(loc, expr, type);
	}

	@Override
	protected boolean needsAssumeInRangeStatement(final CPrimitive type) {
		// We always need to ensure that the value is in range
		return true;
	}

	@Override
	protected Expression convertToUnsigned(final ILocation loc, final Expression operand, final CPrimitive oldType,
			final CPrimitive resultType) {
		// If sizeof(oldType) < sizeof(resultType), we need to apply a wraparound for unsigneds
		if (!mTypeSizes.isUnsigned(oldType)
				|| mTypeSizes.getSize(resultType.getType()) < mTypeSizes.getSize(oldType.getType())) {
			return applyWraparound(loc, resultType, operand);
		}
		return super.convertToUnsigned(loc, operand, oldType, resultType);
	}

	@Override
	protected Expression applyWraparoundForExpression(final ILocation loc, final CPrimitive type,
			final Expression expr) {
		// Apply wraparound to ensure that the expression is in range
		return applyWraparound(loc, type, expr);
	}
}
