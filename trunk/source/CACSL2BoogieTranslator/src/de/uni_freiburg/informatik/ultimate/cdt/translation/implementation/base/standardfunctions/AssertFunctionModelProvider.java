package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;

public class AssertFunctionModelProvider extends FunctionModelProvider {
	public AssertFunctionModelProvider(final Map<String, IASTNode> functionTable,
			final AuxVarInfoBuilder auxVarInfoBuilder, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final ProcedureManager procedureManager,
			final TypeSizes typeSizes, final TranslationSettings settings,
			final ExpressionResultTransformer expressionResultTransformer, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		super(functionTable, auxVarInfoBuilder, nameHandler, expressionTranslation, memoryHandler,
				typeSizeAndOffsetComputer, procedureManager, typeSizes, settings, expressionResultTransformer,
				typeHandler, cEpressionTranslator, dataRaceChecker);
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		/** C standard library functions (from assert.h) to define the 'assert' macro */
		result.add(new FunctionModel("__assert_fail", this::handleAssertFail));
		result.add(new FunctionModel("__assert_func", this::handleAssertFail));
		// TODO: This should not occur in the preprocessed file, but we handle it for now
		result.add(new FunctionModel("assert", this::handleAssert));
		/** C11 static assertion (C language keyword, deprecated in C23) */
		result.add(new FunctionModel("_Static_assert", this::handleStaticAssert));
		/** C23 static assertion (C language keyword) */
		result.add(new FunctionModel("static_assert", this::handleStaticAssert));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

	private Result handleAssertFail(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 4, name, arguments);

		final List<ExpressionResult> argDispatchResults = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			argDispatchResults.add((ExpressionResult) main.dispatch(argument));
		}

		final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(argDispatchResults);
		return erb.addStatement(createAnnotatedAssertOrAssume(loc, name, mSettings.checkAssertions(), Spec.ASSERT,
				ExpressionFactory.createBooleanLiteral(loc, false))).build();
	}

	private Result handleAssert(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult result = mExprResultTransformer
				.transformSwitchRexIntToBool((ExpressionResult) main.dispatch(arguments[0]), loc, node);
		return new ExpressionResultBuilder().addAllExceptLrValue(result).addStatement(createAnnotatedAssertOrAssume(loc,
				name, mSettings.checkAssertions(), Spec.ASSERT, result.getLrValue().getValue())).build();
	}

	/**
	 * Handle C11 or C23 static assertions with or without an explicit message.
	 *
	 * @param main
	 *            the current dispatcher
	 * @param node
	 *            the static assert expression
	 * @param loc
	 *            the location of the static assert
	 * @param name
	 *            the name of the method
	 *
	 * @return {@link ExpressionResult} representing the static assertion
	 */
	private Result handleStaticAssert(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		final int numAssertArgs = arguments.length;

		/* check if signature of assertion is of form 'static_assert(expr)' or 'static_assert(expr, msg)' */
		if (numAssertArgs == 2) {
			/* static C11 or C23 assertion with two arguments (expr and msg) */
			checkArguments(loc, 2, name, arguments);

			if (isStringLiteral(arguments[1])) {
				/* extract string literal value for custom error message */
				final String errorMsg = String.valueOf(((IASTLiteralExpression) arguments[1]).getValue());

				final ExpressionResult result = mExprResultTransformer
						.transformSwitchRexIntToBool((ExpressionResult) main.dispatch(arguments[0]), loc, node);
				return new ExpressionResultBuilder()
						.addAllExceptLrValue(result).addStatement(createAnnotatedAssertOrAssume(loc, name,
								mSettings.checkAssertions(), Spec.ASSERT, result.getLrValue().getValue(), errorMsg))
						.build();
			}
			/* WARNING: this case should be never reached since the msg should be always a string literal */
			throw new IncorrectSyntaxException(loc, "Message parameter of static assert is not a string literal");
		}
		/* static C11 or C23 assertion with one argument (expr) */
		checkArguments(loc, 1, name, arguments);

		/* handle as regular assertion */
		return handleAssert(main, node, loc, name);
	}
}
