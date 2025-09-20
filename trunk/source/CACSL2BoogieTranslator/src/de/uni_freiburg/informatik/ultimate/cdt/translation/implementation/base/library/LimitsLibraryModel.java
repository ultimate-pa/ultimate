/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Model of limits.h (C11 7.10, https://en.cppreference.com/w/c/header/limits), where the minimum and maximum of
 * different types are defined.
 */
public class LimitsLibraryModel implements ILibraryModel {
	private final TypeSizes mTypeSizes;
	private final FunctionModelHelper mHelper;

	public LimitsLibraryModel(final TypeSizes typeSizes, final FunctionModelHelper helper) {
		mTypeSizes = typeSizes;
		mHelper = helper;
	}

	private ExpressionResult getMinValue(final ILocation loc, final CPrimitives type) {
		final var cType = new CPrimitive(type);
		final BigInteger value = mTypeSizes.getMinValueOfPrimitiveType(cType);
		return mHelper.constructIntegerLiteral(loc, value, cType);
	}

	private ExpressionResult getMaxValue(final ILocation loc, final CPrimitives type) {
		final var cType = new CPrimitive(type);
		final BigInteger value = mTypeSizes.getMaxValueOfPrimitiveType(cType);
		return mHelper.constructIntegerLiteral(loc, value, cType);
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		return List.of(new ConstantModel("CHAR_MIN", loc -> getMinValue(loc, CPrimitives.CHAR)),
				new ConstantModel("CHAR_MAX", loc -> getMaxValue(loc, CPrimitives.CHAR)),
				new ConstantModel("SCHAR_MIN", loc -> getMinValue(loc, CPrimitives.SCHAR)),
				new ConstantModel("SCHAR_MAX", loc -> getMaxValue(loc, CPrimitives.SCHAR)),
				new ConstantModel("SHRT_MIN", loc -> getMinValue(loc, CPrimitives.SHORT)),
				new ConstantModel("SHRT_MAX", loc -> getMaxValue(loc, CPrimitives.SHORT)),
				new ConstantModel("INT_MIN", loc -> getMinValue(loc, CPrimitives.INT)),
				new ConstantModel("INT_MAX", loc -> getMaxValue(loc, CPrimitives.INT)),
				new ConstantModel("LONG_MIN", loc -> getMinValue(loc, CPrimitives.LONG)),
				new ConstantModel("LONG_MAX", loc -> getMaxValue(loc, CPrimitives.LONG)),
				new ConstantModel("LLONG_MIN", loc -> getMinValue(loc, CPrimitives.LONGLONG)),
				new ConstantModel("LLONG_MAX", loc -> getMaxValue(loc, CPrimitives.LONGLONG)),
				new ConstantModel("UCHAR_MAX", loc -> getMaxValue(loc, CPrimitives.UCHAR)),
				new ConstantModel("USHRT_MAX", loc -> getMaxValue(loc, CPrimitives.USHORT)),
				new ConstantModel("UINT_MAX", loc -> getMaxValue(loc, CPrimitives.UINT)),
				new ConstantModel("ULONG_MAX", loc -> getMaxValue(loc, CPrimitives.ULONG)),
				new ConstantModel("ULLONG_MAX", loc -> getMaxValue(loc, CPrimitives.ULONGLONG)));
	}

}
