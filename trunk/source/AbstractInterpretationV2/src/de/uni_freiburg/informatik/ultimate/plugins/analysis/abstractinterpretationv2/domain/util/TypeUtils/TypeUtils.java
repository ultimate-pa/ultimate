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

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class TypeUtils {
	public static void consumeVariable(final Consumer<IBoogieVar> varConsumer, final Consumer<IBoogieVar> boolConsumer,
	        final Consumer<IBoogieVar> arrayConsumer, final IBoogieVar variable) {
		assert arrayConsumer == null;
		assert variable != null;

		consumeVariablePerType(varConsumer, boolConsumer, arrayConsumer, variable, variable.getIType());
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
	        final IBoogieVar variable, final IBoogieType type) {
		if (type instanceof PrimitiveType) {
			final PrimitiveType primitiveType = (PrimitiveType) type;

			if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
				boolConsumer.accept(variable);
			} else {
				varConsumer.accept(variable);
			}
		} else if (type instanceof ArrayType) {
			// TODO: Insert arrayConsumer as soon as array support is implemented.
			varConsumer.accept(variable);
		} else if (type instanceof ConstructedType) {
			final ConstructedType ctype = (ConstructedType) type;
			if (ctype.getUnderlyingType() instanceof ConstructedType) {
				throw new UnsupportedOperationException("Nested constructed type found. No idea how to solve this.");
			}
			consumeVariablePerType(varConsumer, boolConsumer, arrayConsumer, variable, ctype.getUnderlyingType());
		} else {
			throw new UnsupportedOperationException("Not implemented: " + type.getClass().getSimpleName());
		}
	}

	public static <R> R applyVariableFunction(final Function<IBoogieVar, R> varFunction,
	        final Function<IBoogieVar, R> boolFunction, final Function<IBoogieVar, R> arrayFunction,
	        final IBoogieVar variable) {
		assert arrayFunction == null;
		assert variable != null;

		return applyVariableFunctionPerType(varFunction, boolFunction, arrayFunction, variable, variable.getIType());
	}

	private static <R> R applyVariableFunctionPerType(final Function<IBoogieVar, R> varFunction,
	        final Function<IBoogieVar, R> boolFunction, final Function<IBoogieVar, R> arrayFunction,
	        final IBoogieVar variable, final IBoogieType type) {
		if (type instanceof PrimitiveType) {
			final PrimitiveType primitiveType = (PrimitiveType) type;

			if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
				return boolFunction.apply(variable);
			} else {
				return varFunction.apply(variable);
			}
		} else if (type instanceof ArrayType) {
			// TODO: Insert arrayFunction as soon as array support is implemented.
			return varFunction.apply(variable);
		} else if (type instanceof ConstructedType) {
			final ConstructedType ctype = (ConstructedType) type;
			if (ctype.getUnderlyingType() instanceof ConstructedType) {
				throw new UnsupportedOperationException("Nested constructed type found. No idea how to solve this.");
			}
			return applyVariableFunctionPerType(varFunction, boolFunction, arrayFunction, variable,
			        ctype.getUnderlyingType());
		} else {
			throw new UnsupportedOperationException("Not implemented: " + type.getClass().getSimpleName());
		}
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
}
