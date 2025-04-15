package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

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

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
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
		return List.of();
	}
}
