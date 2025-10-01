package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation.IFloatingPointHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class BitvectorFloatingPointHandler implements IFloatingPointHandler {
	private final BitvectorTranslation mTranslation;

	public BitvectorFloatingPointHandler(final BitvectorTranslation translation) {
		mTranslation = translation;
	}

	@Override
	public Expression roundToIntegral(final ILocation loc, final Expression argument, final CPrimitive type,
			final Expression roundingMode) {
		final String smtFunctionName = "fp.roundToIntegral";
		mTranslation.declareFloatingPointFunction(loc, smtFunctionName, false, true, type, type);
		return mTranslation.constructCallToSmtFunction(loc, smtFunctionName, type, type,
				new Expression[] { roundingMode, argument });
	}

	@Override
	public Expression sqrt(final ILocation loc, final Expression argument, final CPrimitive type) {
		final String smtFunctionName = "fp.sqrt";
		mTranslation.declareFloatingPointFunction(loc, smtFunctionName, false, true, type, type);
		return mTranslation.constructCallToSmtFunction(loc, smtFunctionName, type, type,
				new Expression[] { mTranslation.getCurrentRoundingMode(), argument });
	}

	@Override
	public Expression abs(final ILocation loc, final Expression argument, final CPrimitive type) {
		final String smtFunctionName = "fp.abs";
		mTranslation.declareFloatingPointFunction(loc, smtFunctionName, false, false, type, type);
		return mTranslation.constructCallToSmtFunction(loc, smtFunctionName, type, type, new Expression[] { argument });
	}

	private Expression constructSmtFloatClassificationFunction(final ILocation loc, final String smtFunctionName,
			final Expression argument, final CPrimitive argumentCType) {
		mTranslation.declareFloatingPointFunction(loc, smtFunctionName, true, false, argumentCType,
				new CPrimitive(CPrimitives.BOOL));
		return mTranslation.constructCallToSmtFunction(loc, smtFunctionName, argumentCType,
				new CPrimitive(CPrimitives.BOOL), new Expression[] { argument });
	}

	@Override
	public Expression isNan(final ILocation loc, final Expression argument, final CPrimitive type) {
		return constructSmtFloatClassificationFunction(loc, "fp.isNaN", argument, type);
	}

	@Override
	public Expression isInfinite(final ILocation loc, final Expression argument, final CPrimitive type) {
		return constructSmtFloatClassificationFunction(loc, "fp.isInfinite", argument, type);
	}

	@Override
	public Expression isNormal(final ILocation loc, final Expression argument, final CPrimitive type) {
		return constructSmtFloatClassificationFunction(loc, "fp.isNormal", argument, type);
	}

	@Override
	public Expression isZero(final ILocation loc, final Expression argument, final CPrimitive type) {
		return constructSmtFloatClassificationFunction(loc, "fp.isZero", argument, type);
	}

	@Override
	public Expression isSubnormal(final ILocation loc, final Expression argument, final CPrimitive type) {
		return constructSmtFloatClassificationFunction(loc, "fp.isSubnormal", argument, type);
	}

	@Override
	public Expression isPositive(final ILocation loc, final Expression argument, final CPrimitive type) {
		return constructSmtFloatClassificationFunction(loc, "fp.isPositive", argument, type);
	}

	private Expression delegateBinaryFloatOperationToSmt(final ILocation loc, final Expression first,
			final Expression second, final String smtFunctionName, final CPrimitive type) {
		mTranslation.declareFloatingPointFunction(loc, smtFunctionName, false, false, type, type, type);
		return mTranslation.constructCallToSmtFunction(loc, smtFunctionName, type, type,
				new Expression[] { first, second });
	}

	@Override
	public Expression min(final ILocation loc, final Expression firstArgument, final Expression secondArgument,
			final CPrimitive type) {
		return delegateBinaryFloatOperationToSmt(loc, firstArgument, secondArgument, "fp.min", type);
	}

	@Override
	public Expression max(final ILocation loc, final Expression firstArgument, final Expression secondArgument,
			final CPrimitive type) {
		return delegateBinaryFloatOperationToSmt(loc, firstArgument, secondArgument, "fp.max", type);
	}

	@Override
	public Expression remainder(final ILocation loc, final Expression firstArgument, final Expression secondArgument,
			final CPrimitive type) {
		return delegateBinaryFloatOperationToSmt(loc, firstArgument, secondArgument, "fp.rem", type);
	}

	@Override
	public Expression createNan(final ILocation loc, final CPrimitive type) {
		return createConstant(loc, BitvectorTranslation.SMT_LIB_NAN, type);
	}

	@Override
	public Expression createInfinity(final ILocation loc, final CPrimitive type) {
		return createConstant(loc, BitvectorTranslation.SMT_LIB_PLUS_INF, type);
	}

	@Override
	public Expression createMinusInfinity(final ILocation loc, final CPrimitive type) {
		return createConstant(loc, BitvectorTranslation.SMT_LIB_MINUS_INF, type);
	}

	@Override
	public Expression createPlusZero(final ILocation loc, final CPrimitive type) {
		return createConstant(loc, BitvectorTranslation.SMT_LIB_PLUS_ZERO, type);
	}

	private Expression createConstant(final ILocation loc, final String smtFunctionName, final CPrimitive type) {
		mTranslation.declareFloatConstant(loc, smtFunctionName, type);
		return mTranslation.constructCallToSmtFunction(loc, smtFunctionName, type, type, new Expression[] {});
	}
}
