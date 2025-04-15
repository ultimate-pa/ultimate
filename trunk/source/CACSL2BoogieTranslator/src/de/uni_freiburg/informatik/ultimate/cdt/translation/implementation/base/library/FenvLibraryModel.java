package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

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

public class FenvLibraryModel implements ILibraryModel {
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
	public Collection<TypeModel> getTypeModels() {
		return List.of();
	}
}
