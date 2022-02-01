/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
 * Abstract class to describe a variable declaration given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 * @author nutz
 */
public abstract class CType {

	/* C type modifiers */
	private final boolean mIsConst;
	private final boolean mIsInline;
	private final boolean mIsRestrict;
	private final boolean mIsVolatile;

	private final boolean mIsExtern;

	/**
	 * Constructor.
	 *
	 * @param isExtern
	 */
	public CType(final boolean isConst, final boolean isInline, final boolean isRestrict, final boolean isVolatile,
			final boolean isExtern) {
		mIsConst = isConst;
		mIsInline = isInline;
		mIsRestrict = isRestrict;
		mIsVolatile = isVolatile;
		mIsExtern = isExtern;
	}

	public boolean isConst() {
		return mIsConst;
	}

	public boolean isInline() {
		return mIsInline;
	}

	public boolean isRestrict() {
		return mIsRestrict;
	}

	public boolean isVolatile() {
		return mIsVolatile;
	}

	public boolean isExtern() {
		return mIsExtern;
	}

	public abstract boolean isIncomplete();

	@Override
	public abstract String toString();

	/**
	 * In C programmers can use typedef to introduce new alternative names for existing types. This is especially
	 * helpful if the referenced type is very complex (e.g., array of structs of arrays) or if the code should be
	 * portable and the referenced type varies from architecture to architecture. In order to improve Ultimate's output
	 * for the user and in order to improve debugability we work as long as possible with the original type and switch
	 * to the underlying type only when this is absolutely necessary.
	 *
	 * @param cType
	 *            CType object
	 * @return the underlying type in case of CNamed, else the input object
	 */
	public CType getUnderlyingType() {
		return this;
	}

	/**
	 * This is a special notion of type compatibility that we use for matching function signatures. -- i.e. for the most
	 * part we say void is "compatible" with everything.. TODO: think about how general this notion is..
	 *
	 * @param cT
	 * @return
	 */
	public abstract boolean isCompatibleWith(CType cT);

	/**
	 * Returns true iff this type is an integer type according to the definition 6.2.5.7 in the C11 standard.
	 */
	public boolean isIntegerType() {
		if (this instanceof CPrimitive) {
			return (((CPrimitive) this).getGeneralType() == CPrimitiveCategory.INTTYPE);
		}
		return this instanceof CEnum;
	}

	/**
	 * Returns true iff this type is a real floating type according to the definition 6.2.5.10 of the C11 standard.
	 */
	public boolean isRealFloatingType() {
		if (this instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) this;
			return cPrimitive.getType() == CPrimitives.FLOAT || cPrimitive.getType() == CPrimitives.DOUBLE
					|| cPrimitive.getType() == CPrimitives.LONGDOUBLE;
		}
		return false;
	}

	/**
	 * Returns true iff this type is a complex type according to the definition 6.2.5.11 of the C11 standard.
	 */
	public boolean isComplexType() {
		if (this instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) this;
			return cPrimitive.getType() == CPrimitives.COMPLEX_FLOAT
					|| cPrimitive.getType() == CPrimitives.COMPLEX_DOUBLE
					|| cPrimitive.getType() == CPrimitives.COMPLEX_LONGDOUBLE;
		}
		return false;
	}

	/**
	 * Returns true iff this type is an floating type according to the definition 6.2.5.11 in the C11 standard.
	 */
	public boolean isFloatingType() {
		if (this instanceof CPrimitive) {
			return (((CPrimitive) this).getGeneralType() == CPrimitiveCategory.FLOATTYPE);
		}
		return false;
	}

	/**
	 * Returns true iff this type is a real type according to the definition 6.2.5.17 in the C11 standard.
	 */
	public boolean isRealType() {
		return isIntegerType() || isRealFloatingType();
	}

	/**
	 * Returns true iff this type is an arithmetic type according to the definition 6.2.5.18 in the C11 standard.
	 */
	public boolean isArithmeticType() {
		return isIntegerType() || isFloatingType();
	}

	/**
	 * Returns true iff this type is a scalar type according to the definition 6.2.5.21 in the C11 standard.
	 */
	public boolean isScalarType() {
		return (this instanceof CPointer) || isArithmeticType();
	}

	public boolean isVoidPointerType() {
		return getUnderlyingType() instanceof CPointer && ((CPointer) getUnderlyingType()).getTargetType()
				.getUnderlyingType().equals(new CPrimitive(CPrimitives.VOID));
	}

	public boolean isVoidType() {
		return getUnderlyingType().equals(new CPrimitive(CPrimitives.VOID));
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mIsConst ? 1231 : 1237);
		result = prime * result + (mIsExtern ? 1231 : 1237);
		result = prime * result + (mIsInline ? 1231 : 1237);
		result = prime * result + (mIsRestrict ? 1231 : 1237);
		result = prime * result + (mIsVolatile ? 1231 : 1237);
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final CType other = (CType) obj;
		if (mIsConst != other.mIsConst) {
			return false;
		}
		if (mIsExtern != other.mIsExtern) {
			return false;
		}
		if (mIsInline != other.mIsInline) {
			return false;
		}
		if (mIsRestrict != other.mIsRestrict) {
			return false;
		}
		if (mIsVolatile != other.mIsVolatile) {
			return false;
		}
		return true;
	}
}
