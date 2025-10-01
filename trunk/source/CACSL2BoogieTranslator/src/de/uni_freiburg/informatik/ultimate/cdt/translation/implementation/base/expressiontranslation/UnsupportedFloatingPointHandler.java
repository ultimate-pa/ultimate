package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation.IFloatingPointHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

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
