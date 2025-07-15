/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Defines the following conversion between pointers and integers. An integer n is converted to the pointer with base
 * address n and offset 0. A pointer p is converted the base address.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class NonBijectiveMappingOneDimensional implements IPointerIntegerConversion {

	protected final ExpressionTranslation mExpressionTranslation;
	private final TypeSizes mTypeSizes;

	public NonBijectiveMappingOneDimensional(final ExpressionTranslation expressionTranslation,
			final TypeSizes typeSizes) {
		mExpressionTranslation = expressionTranslation;
		mTypeSizes = typeSizes;
	}

	@Override
	public ExpressionResult convertPointerToInt(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {

		final RValue pointer = (RValue) rexp.getLrValue();
		final Expression baseAddress = MemoryHandler.getPointerBaseAddress(pointer.getValue(), loc);

		final RValue sum = new RValue(baseAddress, mExpressionTranslation.getCTypeOfPointerComponents());
		final ExpressionResult newRExpr =
				new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(sum).build();
		return mExpressionTranslation.convertIntToInt(loc, newRExpr, newType);
	}

	@Override
	public ExpressionResult convertIntToPointer(final ILocation loc, final ExpressionResult old,
			final CPointer newType) {
		final ExpressionResult rexp =
				mExpressionTranslation.convertIntToInt(loc, old, mExpressionTranslation.getCTypeOfPointerComponents());

		final Expression zero = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);

		final RValue rVal =
				new RValue(MemoryHandler.constructPointerFromBaseAndOffset(rexp.getLrValue().getValue(), zero, loc),
						newType, false, false);
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

}
