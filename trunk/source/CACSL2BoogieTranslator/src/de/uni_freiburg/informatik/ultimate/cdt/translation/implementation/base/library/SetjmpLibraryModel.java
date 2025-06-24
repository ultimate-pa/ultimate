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
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * C11 7.13 Nonlocal jumps <setjmp.h> (https://en.cppreference.com/w/c/header/setjmp)
 */
public class SetjmpLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final ExpressionTranslation mExpressionTranslation;

	public SetjmpLibraryModel(final FunctionModelHelper helper, final ExpressionTranslation expressionTranslation) {
		mHelper = helper;
		mExpressionTranslation = expressionTranslation;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		// longjmp https://en.cppreference.com/w/c/program/longjmp
		// We cannot handle restoring the environment, so we just check if the function is reachable and create an
		// overraproximation for that case
		result.add(new FunctionModel("longjmp", (main, node, loc, name) -> mHelper
				.handleUnsupportedFunctionByOverapproximation(main, loc, name, new CPrimitive(CPrimitives.VOID))));

		// setjmp https://en.cppreference.com/w/c/program/setjmp
		result.add(new FunctionModel("_setjmp", this::handleSetjmp));
		result.add(new FunctionModel("setjmp", this::handleSetjmp));

		return result;
	}

	// For now we do not handle setjmp properly. We crash on longjmp, so it is sufficient to always return 0 for setjmp.
	private Result handleSetjmp(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		return new ExpressionResult(new RValue(
				mExpressionTranslation.constructLiteralForIntegerType(loc, returnType, BigInteger.ZERO), returnType));
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		// Model jmp_buf just with some arbitrary type, we cannot handle it properly anyways.
		return List.of(new TypeModel("jmp_buf", CPointer.voidPointer()));
	}
}
