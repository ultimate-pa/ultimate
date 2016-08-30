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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

/**
 * Evaluator utilities.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class EvaluatorUtils {
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

	/**
	 * Determines the {@link EvaluatorType} depending on the Boogie {@link PrimitiveType} of an {@link Expression}.
	 * 
	 * @param type
	 *            The {@link PrimitiveType} of an {@link Expression}.
	 * @return The corresponding {@link EvaluatorType}.
	 */
	public static EvaluatorType getEvaluatorType(IBoogieType type) {
		if (type instanceof PrimitiveType) {
			final PrimitiveType primitiveType = (PrimitiveType) type;
			final int typeCode = primitiveType.getTypeCode();

			if (typeCode == PrimitiveType.INT) {
				return EvaluatorType.INTEGER;
			} else if (typeCode == PrimitiveType.REAL) {
				return EvaluatorType.REAL;
			} else if (typeCode == PrimitiveType.BOOL) {
				return EvaluatorType.BOOL;
			} else {
				throw new UnsupportedOperationException("Type code " + typeCode + " is not supported.");
			}
		}

		// By default, return real.
		return EvaluatorType.REAL;
	}
}
