/*
 * Copyright (C) 2013-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022-2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2026 University of Freiburg
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.SetjmpHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * C11 7.13 Nonlocal jumps <setjmp.h> (https://en.cppreference.com/w/c/header/setjmp)
 */
public class SetjmpLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final SetjmpHandler mSetjmpHandler;

	public SetjmpLibraryModel(final FunctionModelHelper helper, final ExpressionResultTransformer exprResultTransformer,
			final ExpressionTranslation expressionTranslation, final SetjmpHandler setjmpHandler) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mSetjmpHandler = setjmpHandler;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		// longjmp https://en.cppreference.com/w/c/program/longjmp
		for (final String name : List.of("longjmp", "_longjmp", "siglongjmp", "__longjmp_chk")) {
			result.add(new FunctionModel(name, this::handleLongjmp));
		}

		// setjmp https://en.cppreference.com/w/c/program/setjmp
		// (sigsetjmp has a second argument that only affects the signal mask)
		result.add(new FunctionModel("setjmp", (main, node, loc, name) -> handleSetjmp(main, node, loc, name, 1)));
		result.add(new FunctionModel("_setjmp", (main, node, loc, name) -> handleSetjmp(main, node, loc, name, 1)));
		result.add(new FunctionModel("sigsetjmp", (main, node, loc, name) -> handleSetjmp(main, node, loc, name, 2)));
		result.add(
				new FunctionModel("__sigsetjmp", (main, node, loc, name) -> handleSetjmp(main, node, loc, name, 2)));

		return result;
	}

	private Result handleSetjmp(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name, final int numberOfArgs) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, numberOfArgs, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult env = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc,
				arguments[0]);
		for (int i = 1; i < arguments.length; i++) {
			builder.addAllExceptLrValue(
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[i]));
		}
		final ExpressionResult setjmp = mSetjmpHandler.handleSetjmp(loc, node, env);
		return builder.addAllIncludingLrValue(setjmp).build();
	}

	private Result handleLongjmp(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);
		final ExpressionResult env = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc,
				arguments[0]);
		final ExpressionResult val = mExprResultTransformer.performImplicitConversion(
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]),
				new CPrimitive(CPrimitives.INT), loc);
		return mSetjmpHandler.handleLongjmp(loc, env, val);
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		// Only used if the program has no typedef for jmp_buf. We only need the address of a jmp_buf (as key for the
		// stored environment), so we model it as an array of one long (which decays to a pointer like jmp_buf).
		final CPrimitive boundType = mExpressionTranslation.getCTypeOfPointerComponents();
		final CArray jmpBuf = new CArray(mExpressionTranslation.constructLiteralForIntegerType(
				LocationFactory.createIgnoreCLocation(), boundType, BigInteger.ONE), boundType,
				new CPrimitive(CPrimitives.LONG));
		return List.of(new TypeModel("jmp_buf", jmpBuf));
	}
}
