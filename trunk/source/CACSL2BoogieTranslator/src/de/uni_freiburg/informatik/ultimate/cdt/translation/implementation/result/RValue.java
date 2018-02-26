/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class RValue extends LRValue {

	public Expression value;

	/**
	 * The Value in a ResultExpression that may only be used on the
	 * right-hand side of an assignment, i.e. its corresponding
	 * memory cell may only be read.
	 * @param value
	 */
	public RValue(final Expression value, final CType cType) {
		this(value, cType, false);
		checkType(cType);
	}

	/**
	 * The Value in a ResultExpression that may only be used on the
	 * right-hand side of an assignment, i.e. its corresponding
	 * memory cell may only be read.
	 * @param value
	 */
	public RValue(final Expression value, final CType cType, final boolean boogieBool) {
		this(value, cType, boogieBool, false);
		checkType(cType);
	}

	public RValue(final RValue rval) {
		this(rval.value, rval.getCType(), rval.isBoogieBool(), rval.isIntFromPointer());
	}

	public RValue(final Expression value, final CType cType,
			final boolean isBoogieBool, final boolean isIntFromPointer) {
		super(cType, isBoogieBool, isIntFromPointer);
		checkType(cType);
		this.value = value;
	}

	@Override
	public Expression getValue() {
		return value;
	}

	public void checkType(final CType type) {
		if (type instanceof CArray) {
			throw new IllegalArgumentException("RValues cannot have array type");
		}
		if (type instanceof CFunction) {
			throw new IllegalArgumentException("RValues cannot have function type");
		}
		if (!ExpressionFactory.areBoogieAndCTypeCompatible()) {
			throw new IllegalArgumentException("The value of the constructed RValue has a BoogieType that is "
					+ "incompatible with its CType.");
		}
	}

	static RValue boolToInt(final ILocation loc, final RValue rVal,
			final ExpressionTranslation expressionTranslation) {
		assert rVal.isBoogieBool();
		final Expression one = expressionTranslation.constructLiteralForIntegerType(loc,
				new CPrimitive(CPrimitives.INT), BigInteger.ONE);
		final Expression zero = expressionTranslation.constructLiteralForIntegerType(loc,
				new CPrimitive(CPrimitives.INT), BigInteger.ZERO);
		return new RValue(ExpressionFactory.newIfThenElseExpression(loc, rVal.getValue(), one, zero), rVal.getCType(),
				false);
	}
}
