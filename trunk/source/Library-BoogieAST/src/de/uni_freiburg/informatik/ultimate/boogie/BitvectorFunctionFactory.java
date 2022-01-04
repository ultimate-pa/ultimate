/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Boogie does not provide native support for most bitvector operations of
 * SMT-LIB. These operations are however very helpful for modeling C programs.
 * Hence we developed a convention based on the :smtdefined attibute that allows
 * us to give Boogie functions the semantics of SMT-LIB functions.
 * {@link https://github.com/ultimate-pa/ultimate/wiki/Boogie#attribute-defined-directives}
 * Unfortunately, this was not sufficient. We also have to be able to
 * translate SMT functions back to Boogie functions. Because of that
 * we want to have a uniform construction for all function declarations
 * and all function calls. This class provides these constructions.
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class BitvectorFunctionFactory {

	public static final String AUXILIARY_FUNCTION_PREFIX = "~";

	public static Expression constructInequalityFunction(final ILocation loc, final Expression exp1,
			final Expression exp2, final String functionName, final int bitsize) {
		final String fullFunctionName = AUXILIARY_FUNCTION_PREFIX + functionName + bitsize;
		final Expression result = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] { exp1, exp2 }, BoogieType.TYPE_BOOL);
		return result;
	}

}
