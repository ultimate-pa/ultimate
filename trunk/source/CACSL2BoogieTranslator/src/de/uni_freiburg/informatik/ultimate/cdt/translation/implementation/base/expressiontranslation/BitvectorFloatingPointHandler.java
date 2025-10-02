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
		return mTranslation.constructCallToSmtOperation(loc, smtFunctionName, type,
				new Expression[] { roundingMode, argument });
	}

	@Override
	public Expression sqrt(final ILocation loc, final Expression argument, final CPrimitive type) {
		final String smtFunctionName = "fp.sqrt";
		mTranslation.declareFloatingPointFunction(loc, smtFunctionName, false, true, type, type);
		return mTranslation.constructCallToSmtOperation(loc, smtFunctionName, type,
				new Expression[] { mTranslation.getCurrentRoundingMode(), argument });
	}

	@Override
	public Expression abs(final ILocation loc, final Expression argument, final CPrimitive type) {
		final String smtFunctionName = "fp.abs";
		mTranslation.declareFloatingPointFunction(loc, smtFunctionName, false, false, type, type);
		return mTranslation.constructCallToSmtOperation(loc, smtFunctionName, type, new Expression[] { argument });
	}

	private Expression constructSmtFloatClassificationFunction(final ILocation loc, final String smtFunctionName,
			final Expression argument, final CPrimitive argumentCType) {
		mTranslation.declareFloatingPointFunction(loc, smtFunctionName, true, false, argumentCType,
				new CPrimitive(CPrimitives.BOOL));
		return mTranslation.constructCallToSmtPredicate(loc, smtFunctionName, argumentCType,
				new Expression[] { argument });
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
		return mTranslation.constructCallToSmtOperation(loc, smtFunctionName, type, new Expression[] { first, second });
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
		return mTranslation.constructCallToSmtOperation(loc, smtFunctionName, type, new Expression[] {});
	}
}
