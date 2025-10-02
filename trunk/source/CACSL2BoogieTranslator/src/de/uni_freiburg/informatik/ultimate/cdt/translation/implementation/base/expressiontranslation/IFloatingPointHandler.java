/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public interface IFloatingPointHandler {
	Expression roundToIntegral(ILocation loc, Expression argument, CPrimitive type, Expression roundingMode);

	Expression sqrt(ILocation loc, Expression argument, CPrimitive type);

	Expression abs(ILocation loc, Expression argument, CPrimitive type);

	Expression isNan(ILocation loc, Expression argument, CPrimitive type);

	Expression isInfinite(ILocation loc, Expression argument, CPrimitive type);

	Expression isNormal(ILocation loc, Expression argument, CPrimitive type);

	Expression isZero(ILocation loc, Expression argument, CPrimitive type);

	Expression isSubnormal(ILocation loc, Expression argument, CPrimitive type);

	Expression isPositive(ILocation loc, Expression argument, CPrimitive type);

	Expression createNan(ILocation loc, CPrimitive type);

	Expression createInfinity(ILocation loc, CPrimitive type);

	Expression createMinusInfinity(ILocation loc, CPrimitive type);

	Expression createPlusZero(ILocation loc, CPrimitive type);

	Expression min(ILocation loc, Expression firstArgument, Expression secondArgument, CPrimitive type);

	Expression max(ILocation loc, Expression firstArgument, Expression secondArgument, CPrimitive type);

	Expression remainder(ILocation loc, Expression firstArgument, Expression secondArgument, CPrimitive type);
}
