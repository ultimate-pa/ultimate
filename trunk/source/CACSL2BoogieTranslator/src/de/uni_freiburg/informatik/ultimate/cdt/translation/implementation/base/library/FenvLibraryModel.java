/*
 * Copyright (C) 2013-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022-2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Model of the header fenv.h (see C11 7.6, https://en.cppreference.com/w/c/header/fenv)
 */
public class FenvLibraryModel implements ILibraryModel {
	/*
	 * Hardcoded to the following constants: FE_DOWNWARD 1024 FE_TONEAREST 0 FE_TOWARDZERO 3072 FE_UPWARD 2048
	 */
	public static final BigInteger FE_DOWNWARD = BigInteger.valueOf(1024);
	public static final BigInteger FE_TONEAREST = BigInteger.ZERO;
	public static final BigInteger FE_TOWARDZERO = BigInteger.valueOf(3072);
	public static final BigInteger FE_UPWARD = BigInteger.valueOf(2048);

	private final FunctionModelHelper mHelper;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	public FenvLibraryModel(final FunctionModelHelper helper, final ExpressionResultTransformer exprResultTransformer,
			final ExpressionTranslation expressionTranslation, final AuxVarInfoBuilder auxVarInfoBuilder) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		return List.of(new FunctionModel("fegetround", this::handleBuiltinFegetround),
				new FunctionModel("fesetround", this::handleBuiltinFesetround));
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of("feclearexcept", "fegetexceptflag", "feraiseexcept", "fesetexceptflag", "fetestexcept",
				"fegetenv", "feholdexcept", "fesetenv", "feupdateenv");
	}

	private Result handleBuiltinFegetround(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 0, name, arguments);
		final RValue rvalue = mExpressionTranslation.constructBuiltinFegetround(loc);

		return new ExpressionResultBuilder().setLrValue(rvalue).build();
	}

	private Result handleBuiltinFesetround(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);

		final ExpressionResult decayedArgument =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult convertedArgument =
				mExprResultTransformer.convertIfNecessary(loc, decayedArgument, new CPrimitive(CPrimitives.INT));

		return mExpressionTranslation.constructBuiltinFesetround(loc, convertedArgument, mAuxVarInfoBuilder);
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		final var intType = new CPrimitive(CPrimitives.INT);
		return List.of(
				new ConstantModel("FE_DOWNWARD", loc -> mHelper.constructIntegerLiteral(loc, FE_DOWNWARD, intType)),
				new ConstantModel("FE_TONEAREST", loc -> mHelper.constructIntegerLiteral(loc, FE_TONEAREST, intType)),
				new ConstantModel("FE_TOWARDZERO", loc -> mHelper.constructIntegerLiteral(loc, FE_TOWARDZERO, intType)),
				new ConstantModel("FE_UPWARD", loc -> mHelper.constructIntegerLiteral(loc, FE_UPWARD, intType)));
	}
}
