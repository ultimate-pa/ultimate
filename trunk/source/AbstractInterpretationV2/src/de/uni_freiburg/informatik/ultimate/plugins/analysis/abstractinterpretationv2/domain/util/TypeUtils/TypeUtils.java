/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtils;

import java.util.function.Consumer;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public final class TypeUtils {
	private static final String SORT_BOOL = "Bool";
	private static final String SORT_REAL = "Real";

	private static final Integer ITYPE_INT = PrimitiveType.INT;
	private static final Integer ITYPE_REAL = PrimitiveType.REAL;
	private static final Integer ITYPE_BOOL = PrimitiveType.BOOL;

	private TypeUtils() {
		// do not instantiate utility class
	}

	public static void consumeVariable(final Consumer<IBoogieVar> varConsumer, final Consumer<IBoogieVar> boolConsumer,
			final Consumer<IBoogieVar> arrayConsumer, final IBoogieVar variable) {
		assert arrayConsumer == null;
		assert variable != null;

		consumeVariablePerType(varConsumer, boolConsumer, arrayConsumer, variable);
	}

	public static void consumeVariable(final Consumer<IProgramVarOrConst> varConsumer,
			final Consumer<IProgramVarOrConst> boolConsumer, final Object arrayConsumer,
			final IProgramVarOrConst variable) {
		assert arrayConsumer == null;
		assert variable != null;

		final Sort sort = variable.getTerm().getSort();

		if (sort.isNumericSort()) {
			varConsumer.accept(variable);
		} else if (sort.getName().equals("Bool")) {
			boolConsumer.accept(variable);
		} else if (sort.isArraySort()) {
			// TODO: Insert arrayConsumer as soon as array support is implemented.
			varConsumer.accept(variable);
			// arrayConsumer.equals(variable);
		} else {
			throw new UnsupportedOperationException("Type not supported.");
		}
	}

	private static void consumeVariablePerType(final Consumer<IBoogieVar> varConsumer,
			final Consumer<IBoogieVar> boolConsumer, final Consumer<IBoogieVar> arrayConsumer,
			final IBoogieVar variable) {
		if (isBoolean(variable)) {
			boolConsumer.accept(variable);
		} else if (isNumeric(variable)) {
			varConsumer.accept(variable);
		} else if (isArray(variable)) {
			// TODO: Insert arrayConsumer as soon as array support is implemented.
			varConsumer.accept(variable);
		} else {
			throw new UnsupportedOperationException("Not implemented: " + variable.getSort());
		}
	}

	public static <R> R applyVariableFunction(final Function<IBoogieVar, R> varFunction,
			final Function<IBoogieVar, R> boolFunction, final Function<IBoogieVar, R> arrayFunction,
			final IBoogieVar variable) {
		assert arrayFunction == null;
		assert variable != null;

		return applyVariableFunctionPerType(varFunction, boolFunction, arrayFunction, variable);
	}

	private static <R> R applyVariableFunctionPerType(final Function<IBoogieVar, R> varFunction,
			final Function<IBoogieVar, R> boolFunction, final Function<IBoogieVar, R> arrayFunction,
			final IBoogieVar variable) {

		if (isBoolean(variable)) {
			return boolFunction.apply(variable);
		} else if (isNumeric(variable)) {
			return varFunction.apply(variable);
		} else if (isArray(variable)) {
			// TODO: Insert arrayFunction as soon as array support is implemented.
			return varFunction.apply(variable);
		} else {
			throw new UnsupportedOperationException("Not implemented: " + variable.getSort());
		}
	}

	public static <R> R applyTypeFunction(final Function<Sort, R> intFunction, final Function<Sort, R> realFunction,
			final Function<Sort, R> boolFunction, final Function<Sort, R> arrayFunction, final Sort sort) {
		assert sort != null;
		if (isBoolean(sort)) {
			assert boolFunction != null;
			return boolFunction.apply(sort);
		} else if (isNumericNonInt(sort)) {
			assert realFunction != null;
			return realFunction.apply(sort);
		} else if (isNumeric(sort)) {
			return intFunction.apply(sort);
		} else if (isArray(sort)) {
			assert arrayFunction != null;
			return arrayFunction.apply(sort);
		}
		throw new UnsupportedOperationException("Not implemented: " + sort);
	}

	public static <R> R applyTypeFunction(final Function<IBoogieType, R> intFunction,
			final Function<IBoogieType, R> realFunction, final Function<IBoogieType, R> boolFunction,
			final Function<IBoogieType, R> arrayFunction, final IBoogieType type) {
		assert type != null;

		if (type instanceof PrimitiveType) {
			final PrimitiveType prim = (PrimitiveType) type;
			if (prim == BoogieType.TYPE_BOOL) {
				assert boolFunction != null;
				return boolFunction.apply(type);
			} else if (prim == BoogieType.TYPE_INT) {
				assert intFunction != null;
				return intFunction.apply(type);
			} else if (prim == BoogieType.TYPE_REAL) {
				assert realFunction != null;
				return realFunction.apply(type);
			}
			throw new IllegalArgumentException("Type error: " + prim.getClass().getSimpleName());
		} else if (type instanceof ConstructedType) {
			final ConstructedType ctype = (ConstructedType) type;

			if (ctype.getUnderlyingType() instanceof ConstructedType) {
				throw new UnsupportedOperationException("Nested constructed type found. No idea how to solve this.");
			}
			return applyTypeFunction(intFunction, realFunction, boolFunction, arrayFunction, ctype.getUnderlyingType());
		} else if (type instanceof ArrayType) {
			assert arrayFunction != null;
			return arrayFunction.apply(type);
		}

		throw new UnsupportedOperationException("Type not implemented: " + type.getClass().getSimpleName());
	}

	public static boolean isArray(final Sort sort) {
		return sort.getRealSort().isArraySort();
	}

	private static boolean isNumeric(final Sort sort) {
		return sort.getRealSort().isNumericSort();
	}

	private static boolean isNumericNonInt(final Sort sort) {
		return SORT_REAL.equals(sort.getRealSort().getName());
	}

	private static boolean isBoolean(final Sort sort) {
		return SORT_BOOL.equals(sort.getRealSort().getName());
	}

	public static boolean isBoolean(final IBoogieType type) {
		return ITYPE_BOOL.equals(primitiveType(type));
	}

	public static boolean isNumeric(final IBoogieType type) {
		final Integer t = primitiveType(type);
		return ITYPE_INT.equals(t) || ITYPE_REAL.equals(t);
	}

	public static boolean isNumeric(final IBoogieVar var) {
		return isNumeric(var.getSort());
	}

	public static boolean isBoolean(final IBoogieVar var) {
		return isBoolean(var.getSort());
	}

	private static boolean isArray(final IBoogieVar variable) {
		return isArray(variable.getSort());
	}

	public static boolean isNumericNonInt(final IBoogieType type) {
		return ITYPE_REAL.equals(primitiveType(type));
	}

	public static boolean isNumericNonInt(final IBoogieVar var) {
		return isNumericNonInt(var.getSort());
	}

	public static boolean isNumericInt(final IBoogieType type) {
		return ITYPE_INT.equals(primitiveType(type));
	}

	private static Integer primitiveType(final IBoogieType type) {
		if (type instanceof PrimitiveType) {
			return ((PrimitiveType) type).getTypeCode();
		} else if (type instanceof ConstructedType) {
			final ConstructedType ctype = (ConstructedType) type;
			if (ctype.getUnderlyingType() instanceof ConstructedType) {
				return null;
			}
			return primitiveType(ctype.getUnderlyingType());
		}
		return null;
	}

	/**
	 * Checks if two Boogie types are of the same type category. There are three type categories:
	 * <ul>
	 * <li>numeric (int, real)</li>
	 * <li>boolean (bool)</li>
	 * <li>unsupported (bit-vectors, arrays, ...)</li>
	 * </ul>
	 *
	 * @param a
	 *            first type
	 * @param b
	 *            second type
	 * @return a and b are of the same type category
	 */
	public static boolean categoryEquals(final IBoogieType a, final IBoogieType b) {
		return (isBoolean(a) == isBoolean(b)) && (isNumeric(a) == isNumeric(b));
	}

	public static boolean isIntTerm(final Term t) {
		return "Int".equals(t.getSort().getRealSort().getName());
	}

	public static boolean isRealTerm(final Term t) {
		return "Real".equals(t.getSort().getRealSort().getName());
	}

	public static Sort getInnermostArrayValueSort(final Sort sort) {
		Sort currentSort = sort;
		while (currentSort.isArraySort()) {
			currentSort = getValueSort(sort);
		}
		return currentSort;
	}

	public static Sort getValueSort(final Sort sort) {
		if (!sort.isArraySort()) {
			throw new IllegalArgumentException("sort is no array sort: " + sort);
		}
		return sort.getArguments()[1];
	}

	public static Sort getIndexSort(final Sort sort) {
		if (!sort.isArraySort()) {
			throw new IllegalArgumentException("sort is no array sort: " + sort);
		}
		return sort.getArguments()[0];
	}
}
