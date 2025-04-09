package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class RandomStandardFunctionHandler extends StandardFunctionHandler2 {
	public RandomStandardFunctionHandler(final Map<String, IASTNode> functionTable,
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

		/**
		 * 7.22.2.1 The rand function
		 *
		 * see https://en.cppreference.com/w/c/numeric/random/rand
		 *
		 * Pseudo-random integer value between ​0​ and RAND_MAX, inclusive. The value of the RAND_MAX macro shall be at
		 * least 32767.
		 *
		 * We handle this similar to handleVerifierNonDet, but we limit the return type to positive range of int.
		 *
		 * We ignore seeding with srand.
		 */
		result.add(new FunctionModel("rand", this::handleRand));

		/**
		 * 7.22.2.2 The srand function
		 *
		 * see https://en.cppreference.com/w/c/numeric/random/srand
		 *
		 * The srand function uses the argument as a seed for a new sequence of pseudo-random numbers to be returned by
		 * subsequent calls to rand.
		 *
		 * We can safely skip this function.
		 */
		result.add(new FunctionModel("srand",
				(main, node, loc, name) -> handleVoidFunctionBySkipAndDispatch(main, node, loc, name, 1)));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

	private Result handleRand(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		checkArguments(loc, 0, name, node.getArguments());

		final CPrimitive cType = new CPrimitive(CPrimitives.INT);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		resultBuilder.addAuxVarWithDeclaration(auxvarinfo);

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), cType);
		resultBuilder.setLrValue(returnValue);

		final Expression expr = returnValue.getValue();
		final Expression minValue = mTypeSizes.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO);
		final Expression maxValue =
				mTypeSizes.constructLiteralForIntegerType(loc, cType, mTypeSizes.getMaxValueOfPrimitiveType(cType));

		final Expression biggerMinInt = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, minValue, cType, expr, cType);
		final Expression smallerMaxValue = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, expr, cType, maxValue, cType);
		final AssumeStatement inRange = new AssumeStatement(loc, ExpressionFactory.newBinaryExpression(loc,
				BinaryExpression.Operator.LOGICAND, biggerMinInt, smallerMaxValue));
		resultBuilder.addStatement(inRange);

		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		return resultBuilder.build();
	}
}
