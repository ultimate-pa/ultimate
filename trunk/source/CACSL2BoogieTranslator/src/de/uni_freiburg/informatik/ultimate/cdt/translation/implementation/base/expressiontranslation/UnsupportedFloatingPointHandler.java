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

/**
 * Implementation of {@link IFloatingPointHandler} that crashes whenever any method is invoked, which can be used when
 * floating-point operations are not supported (e.g., in {@link IntegerTranslation}).
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class UnsupportedFloatingPointHandler implements IFloatingPointHandler {
	private static final String NOT_IMPLEMENTED = "Operation is not yet implemented in non-bitprecise translation.";

	@Override
	public Expression roundToIntegral(final ILocation loc, final Expression argument, final CPrimitive type,
			final Expression roundingMode) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression sqrt(final ILocation loc, final Expression argument, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression abs(final ILocation loc, final Expression argument, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression isNan(final ILocation loc, final Expression argument, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression isInfinite(final ILocation loc, final Expression argument, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression isNormal(final ILocation loc, final Expression argument, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression isZero(final ILocation loc, final Expression argument, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression isSubnormal(final ILocation loc, final Expression argument, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression isPositive(final ILocation loc, final Expression argument, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression createNan(final ILocation loc, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression createInfinity(final ILocation loc, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression createMinusInfinity(final ILocation loc, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression createPlusZero(final ILocation loc, final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression min(final ILocation loc, final Expression firstArgument, final Expression secondArgument,
			final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression max(final ILocation loc, final Expression firstArgument, final Expression secondArgument,
			final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression remainder(final ILocation loc, final Expression firstArgument, final Expression secondArgument,
			final CPrimitive type) {
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}
}
