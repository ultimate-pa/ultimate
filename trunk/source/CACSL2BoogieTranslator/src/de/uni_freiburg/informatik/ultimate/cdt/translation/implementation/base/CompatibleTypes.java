/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Objects;
import java.util.OptionalInt;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion.StructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

/**
 * Provides static methods to determine if given C types are compatible, as specified in Section 6.2.7 of the C11
 * standard.
 */
public final class CompatibleTypes {
	private CompatibleTypes() {
		// static class
	}

	/**
	 * Checks if two given types are "compatible", as specified in C11 6.2.7.
	 *
	 * Note: The "compatible" relation is symmetric and reflexive, but not transitive (e.g. two different enum types are
	 * both compatible with int but not with each other).
	 *
	 * @param type1
	 *            the first type
	 * @param type2
	 *            the second type
	 *
	 * @return {@code true} if the given types are compatible, {@code false} otherwise
	 */
	public static boolean areCompatible(final ICType type1, final ICType type2) {
		return areCompatible(type1, type2, new SymmetricHashRelation<>());
	}

	private static boolean areCompatible(final ICType type1, final ICType type2,
			final SymmetricHashRelation<ICType> visitedPairs) {
		// Implementation based on the summary at cppreference.com, as of September 18, 2025.
		// <https://en.cppreference.com/w/c/language/compatible_type.html#Compatible_types>

		if (type1 == type2) {
			// C11 6.2.7 §1: Two types have compatible type if their types are the same.
			// Note: The use of reference equality (==) above is intentional, as ICType::equals would (redundantly) have
			// to do the same recursion we implement here.
			return true;
		}

		if (visitedPairs.containsPair(type1, type2)) {
			// We found a cycle in the C type (e.g. a linked list struct type containing a pointer to the same linked
			// list struct type). As long as we do not find any other counterexample to compatibility, the types are
			// indeed compatible. Thus, we return true here.
			// (This probably means compatibility is formally defined as some kind of greatest fixpoint.)
			return true;
		}

		// Resolve typedef names.
		// C11 6.7.8 §3: A typedef declaration does not introduce a new type, only a synonym for the type so specified.
		final ICType actualType1 = type1.getUnderlyingType();
		final ICType actualType2 = type2.getUnderlyingType();

		return switch (actualType1) {
		case final CArray array1 ->
				actualType2 instanceof final CArray array2 && areCompatibleArrayTypes(array1, array2, visitedPairs);

		case final CEnum enum1 -> (actualType2 instanceof final CEnum enum2 && areCompatibleEnumTypes(enum1, enum2))
				|| (actualType2 instanceof final CPrimitive primitive2
						&& isCompatiblePrimitiveForEnum(enum1, primitive2));

		case final CFunction function1 -> actualType2 instanceof final CFunction function2
				&& areCompatibleFunctionTypes(function1, function2, visitedPairs);

		case final CNamed named1 -> throw new AssertionError("getUnderlyingType() must not return CNamed");

		// C11 6.7.6.1 §2: For two pointer types to be compatible, both shall be identically qualified and both shall be
		// pointers to compatible types.
		// (Note: We currently do not track type qualifiers.)
		case final CPointer pointer1 -> actualType2 instanceof final CPointer pointer2
				&& areCompatible(pointer1.getPointsToType(), pointer2.getPointsToType(), visitedPairs);

		case final CPrimitive primitive1 -> (actualType2 instanceof final CPrimitive primitive2
				&& primitive1.getType() == primitive2.getType())
				|| (actualType2 instanceof final CEnum enum2 && isCompatiblePrimitiveForEnum(enum2, primitive1));

		case final CStructOrUnion structOrUnion1 -> actualType2 instanceof final CStructOrUnion structOrUnion2
				&& areCompatibleStructOrUnionTypes(structOrUnion1, structOrUnion2, visitedPairs);
		};
	}

	private static boolean areCompatibleEnumTypes(final CEnum enum1, final CEnum enum2) {
		// C 6.2.7 §1: If one is declared with a tag, the other shall be declared with the same tag.
		// (Note: If neither is declared with a tag, we test for equality of two empty strings.)
		if (!Objects.equals(enum1.getName(), enum2.getName())) {
			return false;
		}

		// C11 6.2.7 §1: If both are completed anywhere within their respective translation units, then the following
		// additional requirements apply: [...]
		if (enum1.isIncomplete() || enum2.isIncomplete()) {
			return true;
		}

		// C11 6.2.7 §1: [...] there shall be a one-to-one correspondence between their members such that [...]
		if (enum1.getFieldCount() != enum2.getFieldCount()) {
			return false;
		}

		// C11 6.2.7 §1: [...] For two enumerations, corresponding members shall have the same values.
		// (Note: We do not track values in the type, and instead check if the enum constants are in the same order.)
		for (int i = 0; i < enum1.getFieldCount(); i++) {
			if (!enum1.getFieldIds()[i].equals(enum2.getFieldIds()[i])) {
				return false;
			}
		}

		return true;
	}

	private static boolean isCompatiblePrimitiveForEnum(final CEnum enum1, final CPrimitive primitive2) {
		// C11 6.7.2.2 §4: Each enumerated type shall be compatible with char, a signed integer type, or an
		// unsigned integer type. The choice of type is implementation-defined
		// (Note: In Ultimate, enumeration types are always compatible with int.)
		return primitive2.getType() == CPrimitives.INT;
	}

	private static boolean areCompatibleFunctionTypes(final CFunction function1, final CFunction function2,
			final SymmetricHashRelation<ICType> visitedPairs) {
		visitedPairs.addPair(function1, function2);

		// C11 6.7.6.3 §15: For two function types to be compatible, both shall specify compatible return types. [...]
		if (!areCompatible(function1.getResultType(), function2.getResultType(), visitedPairs)) {
			return false;
		}

		// C11 6.7.6.3 §15: [...] Moreover, the parameter type lists, if both are present, shall agree in the number of
		// parameters and in use of the ellipsis terminator; [...]
		// (Note: CFunction does not track whether or not the parameter list is present.)
		if (function1.getParameterTypes().length != function2.getParameterTypes().length
				|| function1.hasVarArgs() != function2.hasVarArgs()) {
			return false;
		}

		// C11 6.7.6.3 §15: [...] corresponding parameters shall have compatible types.
		for (int i = 0; i < function1.getParameterTypes().length; i++) {
			if (!areCompatible(function1.getParameterTypes()[i].getType(), function2.getParameterTypes()[i].getType(),
					visitedPairs)) {
				return false;
			}
		}

		return true;
	}

	private static boolean areCompatibleStructOrUnionTypes(final CStructOrUnion structOrUnion1,
			final CStructOrUnion structOrUnion2, final SymmetricHashRelation<ICType> visitedPairs) {
		visitedPairs.addPair(structOrUnion1, structOrUnion2);

		// A struct is not compatible to a union.
		if (structOrUnion1.isStructOrUnion() != structOrUnion2.isStructOrUnion()) {
			return false;
		}

		// C11 6.2.7 §1: If one is declared with a tag, the other shall be declared with the same tag.
		// (Note: If neither is declared with a tag, we test for equality of two empty strings.)
		if (!Objects.equals(structOrUnion1.getName(), structOrUnion2.getName())) {
			return false;
		}

		// C11 6.2.7 §1: If both are completed anywhere within their respective translation units, then the following
		// additional requirements apply: [...]
		if (structOrUnion1.isIncomplete() || structOrUnion2.isIncomplete()) {
			return true;
		}

		// C11 6.2.7 §1: [...] there shall be a one-to-one correspondence between their members such that [...]
		if (structOrUnion1.getFieldCount() != structOrUnion2.getFieldCount()) {
			return false;
		}

		// C11 6.2.7 §1: [...] if one member of the pair is declared with a name, the other is declared with the same
		// name. For two structures, corresponding members shall be declared in the same order.
		final var lookup =
				structOrUnion1.isStructOrUnion() == StructOrUnion.STRUCT ? makeStructFieldLookup(structOrUnion2)
						: makeUnionFieldLookup(structOrUnion2);

		for (int index1 = 0; index1 < structOrUnion1.getFieldCount(); ++index1) {
			final String id = structOrUnion1.getFieldIds()[index1];
			final OptionalInt index2 = lookup.apply(index1, id);
			if (index2.isEmpty()) {
				// (no one-to-one corresponding member found)
				return false;
			}

			// C11 6.2.7 §1: [...] each pair of corresponding members are declared with compatible types; [...]
			if (!areCompatible(structOrUnion1.getFieldTypes()[index1],
					structOrUnion2.getFieldTypes()[index2.getAsInt()], visitedPairs)) {
				return false;
			}
			// C11 6.2.7 §1: [...] corresponding bit-fields shall have the same widths.
			if (structOrUnion1.getBitfieldWidth(id) != structOrUnion2.getBitfieldWidth(id)) {
				return false;
			}
		}

		// all requirements satisfied
		return true;
	}

	private static BiFunction<Integer, String, OptionalInt> makeStructFieldLookup(final CStructOrUnion structType) {
		assert structType.isStructOrUnion() == StructOrUnion.STRUCT;
		return (index, id) -> {
			if (index >= structType.getFieldCount() || !Objects.equals(id, structType.getFieldIds()[index])) {
				return OptionalInt.empty();
			}
			return OptionalInt.of(index);
		};
	}

	private static BiFunction<Integer, String, OptionalInt> makeUnionFieldLookup(final CStructOrUnion unionType) {
		assert unionType.isStructOrUnion() == StructOrUnion.UNION;
		return (index, id) -> {
			if (index >= unionType.getFieldCount()) {
				return OptionalInt.empty();
			}
			if (Objects.equals(id, unionType.getFieldIds()[index])) {
				// Shortcut for efficiency
				return OptionalInt.of(index);
			}
			final int actualIndex = Arrays.asList(unionType.getFieldIds()).indexOf(id);
			return actualIndex == -1 ? OptionalInt.empty() : OptionalInt.of(actualIndex);
		};
	}

	private static boolean areCompatibleArrayTypes(final CArray array1, final CArray array2,
			final SymmetricHashRelation<ICType> visitedPairs) {
		// C11 6.7.6.2 §6: For two array types to be compatible, both shall have compatible element types, and if both
		// size specifiers are present, and are integer constant expressions, then both size specifiers shall have the
		// same constant value.

		if (!areCompatible(array1.getValueType(), array2.getValueType(), visitedPairs)) {
			return false;
		}
		if (array1.isIncomplete() || array2.isIncomplete()) {
			return true;
		}
		final BigInteger bound1 = CTranslationUtil.extractIntegerValue(array1.getBound().getValue());
		final BigInteger bound2 = CTranslationUtil.extractIntegerValue(array2.getBound().getValue());
		return bound1 == null || bound2 == null || bound1.equals(bound2);
	}
}
