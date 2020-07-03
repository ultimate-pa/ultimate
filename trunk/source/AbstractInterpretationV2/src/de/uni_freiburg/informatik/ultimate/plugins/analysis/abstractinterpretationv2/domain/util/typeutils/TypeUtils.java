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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils;

import java.util.function.Consumer;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

public final class TypeUtils {

	private static final Integer ITYPE_INT = BoogiePrimitiveType.INT;
	private static final Integer ITYPE_REAL = BoogiePrimitiveType.REAL;
	private static final Integer ITYPE_BOOL = BoogiePrimitiveType.BOOL;

	private TypeUtils() {
		// do not instantiate utility class
	}

	// TODO: Implement better handling of types. Make it more generic!

	public static <VARDECL> void consumeVariable(final Consumer<VARDECL> varConsumer,
			final Consumer<VARDECL> boolConsumer, final Consumer<VARDECL> arrayConsumer, final VARDECL variable) {
		assert arrayConsumer == null;
		assert variable != null;

		consumeVariablePerType(varConsumer, boolConsumer, arrayConsumer, variable);
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	private static <VARDECL> void consumeVariablePerType(final Consumer varConsumer, final Consumer boolConsumer,
			final Consumer arrayConsumer, final VARDECL variable) {
		if (variable instanceof IProgramVar) {
			final IProgramVar boogieVar = (IProgramVar) variable;
			if (SmtSortUtils.isBoolSort(boogieVar.getSort())) {
				boolConsumer.accept(variable);
			} else if (SmtSortUtils.isNumericSort(boogieVar.getSort())) {
				varConsumer.accept(variable);
			} else if (SmtSortUtils.isArraySort(boogieVar.getSort())) {
				// TODO: Insert arrayConsumer as soon as array support is implemented.
				varConsumer.accept(variable);
			} else {
				throw new UnsupportedOperationException("Not implemented: " + boogieVar.getSort());
			}
		} else if (variable instanceof IProgramVarOrConst) {
			final IProgramVarOrConst programVar = (IProgramVarOrConst) variable;
			final Sort sort = programVar.getTerm().getSort();
			if (SmtSortUtils.isBoolSort(sort)) {
				boolConsumer.accept(variable);
			} else if (SmtSortUtils.isNumericSort(sort)) {
				varConsumer.accept(variable);
			} else if (SmtSortUtils.isArraySort(sort)) {
				// TODO: Insert arrayConsumer as soon as array support is implemented.
				varConsumer.accept(variable);
			} else {
				throw new UnsupportedOperationException("Not implemented: " + sort);
			}
		} else {
			throw new UnsupportedOperationException("Unknown variable type: " + variable.getClass().getSimpleName());
		}

	}

	public static <R, VARDECL> R applyVariableFunction(final Function<VARDECL, R> varFunction,
			final Function<VARDECL, R> boolFunction, final Function<VARDECL, R> arrayFunction, final VARDECL variable) {
		assert arrayFunction == null;
		assert variable != null;

		return applyVariableFunctionPerType(varFunction, boolFunction, arrayFunction, variable);
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	private static <R, VARDECL> R applyVariableFunctionPerType(final Function varFunction, final Function boolFunction,
			final Function arrayFunction, final VARDECL variable) {
		if (variable instanceof IProgramVar) {
			final IProgramVar boogieVar = (IProgramVar) variable;
			if (SmtSortUtils.isBoolSort(boogieVar.getSort())) {
				return (R) boolFunction.apply(variable);
			} else if (SmtSortUtils.isNumericSort(boogieVar.getSort())) {
				return (R) varFunction.apply(variable);
			} else if (SmtSortUtils.isArraySort(boogieVar.getSort())) {
				// TODO: Insert arrayFunction as soon as array support is implemented.
				return (R) varFunction.apply(variable);
			} else {
				throw new UnsupportedOperationException("Not implemented: " + boogieVar.getSort());
			}
		} else if (variable instanceof IProgramVarOrConst) {
			final IProgramVarOrConst programVar = (IProgramVarOrConst) variable;
			final Sort sort = programVar.getTerm().getSort();
			if (SmtSortUtils.isBoolSort(sort)) {
				return (R) boolFunction.apply(variable);
			} else if (SmtSortUtils.isNumericSort(sort)) {
				return (R) varFunction.apply(variable);
			} else if (SmtSortUtils.isArraySort(sort)) {
				// TODO: Insert arrayFunction as soon as array support is implemented.
				return (R) varFunction.apply(variable);
			} else {
				throw new UnsupportedOperationException("Not implemented: " + sort);
			}
		} else {
			throw new UnsupportedOperationException("Unknown variable type: " + variable.getClass().getSimpleName());
		}

	}

	public static <R> R applyTypeFunction(final Function<Sort, R> intFunction, final Function<Sort, R> realFunction,
			final Function<Sort, R> boolFunction, final Function<Sort, R> arrayFunction, final Sort sort) {
		assert sort != null;
		if (SmtSortUtils.isBoolSort(sort)) {
			assert boolFunction != null;
			return boolFunction.apply(sort);
		} else if (SmtSortUtils.isRealSort(sort)) {
			assert realFunction != null;
			return realFunction.apply(sort);
		} else if (SmtSortUtils.isNumericSort(sort)) {
			return intFunction.apply(sort);
		} else if (SmtSortUtils.isArraySort(sort)) {
			assert arrayFunction != null;
			return arrayFunction.apply(sort);
		}
		throw new UnsupportedOperationException("Not implemented: " + sort);
	}

	public static <R> R applyTypeFunction(final Function<IBoogieType, R> intFunction,
			final Function<IBoogieType, R> realFunction, final Function<IBoogieType, R> boolFunction,
			final Function<IBoogieType, R> arrayFunction, final IBoogieType type) {
		assert type != null;

		if (type instanceof BoogiePrimitiveType) {
			final BoogiePrimitiveType prim = (BoogiePrimitiveType) type;
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
		} else if (type instanceof BoogieConstructedType) {
			final BoogieConstructedType ctype = (BoogieConstructedType) type;

			if (ctype.getUnderlyingType() instanceof BoogieConstructedType) {
				throw new UnsupportedOperationException("Nested constructed type found. No idea how to solve this.");
			}
			return applyTypeFunction(intFunction, realFunction, boolFunction, arrayFunction, ctype.getUnderlyingType());
		} else if (type instanceof BoogieArrayType) {
			assert arrayFunction != null;
			return arrayFunction.apply(type);
		}

		throw new UnsupportedOperationException("Type not implemented: " + type.getClass());
	}

	public static boolean isBoolean(final IBoogieType type) {
		return ITYPE_BOOL.equals(primitiveType(type));
	}

	public static boolean isNumeric(final IBoogieType type) {
		final Integer t = primitiveType(type);
		return ITYPE_INT.equals(t) || ITYPE_REAL.equals(t);
	}

	public static boolean isNumericNonInt(final IBoogieType type) {
		return ITYPE_REAL.equals(primitiveType(type));
	}

	public static boolean isNumericInt(final IBoogieType type) {
		return ITYPE_INT.equals(primitiveType(type));
	}

	private static Integer primitiveType(final IBoogieType type) {
		if (type instanceof BoogiePrimitiveType) {
			return ((BoogiePrimitiveType) type).getTypeCode();
		} else if (type instanceof BoogieConstructedType) {
			final BoogieConstructedType ctype = (BoogieConstructedType) type;
			if (ctype.getUnderlyingType() instanceof BoogieConstructedType) {
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
		return isBoolean(a) == isBoolean(b) && isNumeric(a) == isNumeric(b);
	}

	public static Sort getInnermostArrayValueSort(final Sort sort) {
		Sort currentSort = sort;
		while (currentSort.isArraySort()) {
			currentSort = getValueSort(currentSort);
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
