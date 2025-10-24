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

/**
 * Interface to model types as defined in 6.2.5 in the C11 standard.
 *
 * @author Markus Lindenmann
 * @date 18.09.2012
 * @author nutz
 */
public sealed interface ICType permits CArray, CEnum, CFunction, CNamed, CPointer, CPrimitive, CStructOrUnion {
	/**
	 * Returns true iff this type is incomplete according to the definition 6.2.5.1/19/22/23 in the C11 standard.
	 */
	boolean isIncomplete();

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
	default ICType getUnderlyingType() {
		return this;
	}

	/**
	 * Returns true iff this type is an integer type according to the definition 6.2.5.7 in the C11 standard.
	 */
	default boolean isIntegerType() {
		return false;
	}

	/**
	 * Returns true iff this type is a real floating type according to the definition 6.2.5.10 of the C11 standard.
	 */
	default boolean isRealFloatingType() {
		return false;
	}

	/**
	 * Returns true iff this type is an floating type according to the definition 6.2.5.11 in the C11 standard.
	 */
	default boolean isFloatingType() {
		return false;
	}

	/**
	 * Returns true iff this type is a complex type according to the definition 6.2.5.11 of the C11 standard.
	 */
	default boolean isComplexType() {
		return false;
	}

	/**
	 * Returns true iff this type is a real type according to the definition 6.2.5.17 in the C11 standard.
	 */
	default boolean isRealType() {
		return isIntegerType() || isRealFloatingType();
	}

	/**
	 * Returns true iff this type is an arithmetic type according to the definition 6.2.5.18 in the C11 standard.
	 */
	default boolean isArithmeticType() {
		return isIntegerType() || isFloatingType();
	}

	/**
	 * Returns true iff this type is a scalar type according to the definition 6.2.5.21 in the C11 standard.
	 */
	default boolean isScalarType() {
		return isArithmeticType();
	}

	/**
	 * Returns true iff this type is a void pointer according to the definition 6.3.2.3.3 in the C11 standard.
	 */
	default boolean isVoidPointerType() {
		return false;
	}

	/**
	 * Returns true iff this type is void according to the definition 6.2.5.19 in the C11 standard.
	 */
	default boolean isVoidType() {
		return false;
	}

	/**
	 * Returns true iff this type is atomic according to the definition 6.2.5.27 in the C11 standard.
	 */
	boolean isAtomic();

	@Override
	int hashCode();

	@Override
	boolean equals(final Object obj);

	@Override
	String toString();
}
