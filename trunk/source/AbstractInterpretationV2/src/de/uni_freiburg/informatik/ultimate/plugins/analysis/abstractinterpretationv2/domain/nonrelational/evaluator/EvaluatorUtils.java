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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;

/**
 * Evaluator utilities.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class EvaluatorUtils {
	/**
	 * The type of the evaluator. Determines whether integer operations should be assumed, whether there are real-valued
	 * operations, or whether the evaluator is boolean valued.
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum EvaluatorType {
		REAL, INTEGER, BOOL
	}

	private EvaluatorUtils() {
		// prevent initialization of utility class
	}

	/**
	 * Determines the {@link EvaluatorType} depending on the Boogie {@link BoogiePrimitiveType} of an {@link Expression}.
	 *
	 * @param type
	 *            The {@link BoogiePrimitiveType} of an {@link Expression}.
	 * @return The corresponding {@link EvaluatorType}.
	 */
	public static EvaluatorType getEvaluatorType(final IProgramVar var) {
		final Function<Sort, EvaluatorType> intFunction = t -> EvaluatorType.INTEGER;
		final Function<Sort, EvaluatorType> realFunction = t -> EvaluatorType.REAL;
		final Function<Sort, EvaluatorType> boolFunction = t -> EvaluatorType.BOOL;
		final Function<Sort, EvaluatorType> arrayFunction = t -> {
			return TypeUtils.applyTypeFunction(intFunction, realFunction, boolFunction, null,
					TypeUtils.getInnermostArrayValueSort(t));
		};
		return TypeUtils.applyTypeFunction(intFunction, realFunction, boolFunction, arrayFunction, var.getSort());
	}

	/**
	 * Determines the {@link EvaluatorType} depending on the Boogie {@link BoogiePrimitiveType} of an {@link Expression}.
	 *
	 * @param type
	 *            The {@link BoogiePrimitiveType} of an {@link Expression}.
	 * @return The corresponding {@link EvaluatorType}.
	 */
	public static EvaluatorType getEvaluatorType(final IProgramVarOrConst var) {
		final Function<Sort, EvaluatorType> intFunction = t -> EvaluatorType.INTEGER;
		final Function<Sort, EvaluatorType> realFunction = t -> EvaluatorType.REAL;
		final Function<Sort, EvaluatorType> boolFunction = t -> EvaluatorType.BOOL;
		final Function<Sort, EvaluatorType> arrayFunction = t -> {
			return TypeUtils.applyTypeFunction(intFunction, realFunction, boolFunction, null,
					TypeUtils.getInnermostArrayValueSort(t));
		};
		return TypeUtils.applyTypeFunction(intFunction, realFunction, boolFunction, arrayFunction,
				var.getTerm().getSort());
	}

	/**
	 * Determines the {@link EvaluatorType} depending on the Boogie {@link BoogiePrimitiveType} of an {@link Expression}.
	 *
	 * @param type
	 *            The {@link BoogiePrimitiveType} of an {@link Expression}.
	 * @return The corresponding {@link EvaluatorType}.
	 */
	public static EvaluatorType getEvaluatorType(final IBoogieType type) {
		final Function<IBoogieType, EvaluatorType> intFunction = t -> EvaluatorType.INTEGER;
		final Function<IBoogieType, EvaluatorType> realFunction = t -> EvaluatorType.REAL;
		final Function<IBoogieType, EvaluatorType> boolFunction = t -> EvaluatorType.BOOL;
		final Function<IBoogieType, EvaluatorType> arrayFunction =
				new ArrayFunction(type, intFunction, realFunction, boolFunction);

		return TypeUtils.applyTypeFunction(intFunction, realFunction, boolFunction, arrayFunction, type);
	}

	/**
	 * ArrayFunction to reference itself.
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class ArrayFunction implements Function<IBoogieType, EvaluatorType> {

		private final IBoogieType mType;
		private final Function<IBoogieType, EvaluatorType> mIntFunction;
		private final Function<IBoogieType, EvaluatorType> mRealFunction;
		private final Function<IBoogieType, EvaluatorType> mBoolFunction;

		private ArrayFunction(final IBoogieType type, final Function<IBoogieType, EvaluatorType> intFunction,
				final Function<IBoogieType, EvaluatorType> realFunction,
				final Function<IBoogieType, EvaluatorType> boolFunction) {
			mType = type;
			mIntFunction = intFunction;
			mRealFunction = realFunction;
			mBoolFunction = boolFunction;
		}

		@Override
		public EvaluatorType apply(final IBoogieType t) {
			final BoogieArrayType arrType = (BoogieArrayType) mType;
			return TypeUtils.applyTypeFunction(mIntFunction, mRealFunction, mBoolFunction,
					new ArrayFunction(t, mIntFunction, mRealFunction, mBoolFunction), arrType.getValueType());
		}

	}
}
