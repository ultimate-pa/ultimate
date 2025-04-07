package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationResultReporter;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class LinuxStandardFunctionHandler extends StandardFunctionHandler2 {
	public LinuxStandardFunctionHandler(final ILogger logger, final Map<String, IASTNode> functionTable,
			final AuxVarInfoBuilder auxVarInfoBuilder, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final ProcedureManager procedureManager,
			final CTranslationResultReporter reporter, final TypeSizes typeSizes, final FlatSymbolTable symboltable,
			final TranslationSettings settings, final ExpressionResultTransformer expressionResultTransformer,
			final LocationFactory locationFactory, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		super(logger, functionTable, auxVarInfoBuilder, nameHandler, expressionTranslation, memoryHandler,
				typeSizeAndOffsetComputer, procedureManager, reporter, typeSizes, symboltable, settings,
				expressionResultTransformer, locationFactory, typeHandler, cEpressionTranslator, dataRaceChecker);
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		return List.of(
				/** https://www.man7.org/linux/man-pages/man3/sleep.3.html **/
				new FunctionModel("sleep", this::handleSleep),
				/**
				 * https://linux.die.net/man/3/ntohs "htonl, htons, ntohl, ntohs - convert values between host and
				 * network byte order"
				 *
				 * We simply overapproximate those functions.
				 */
				new FunctionModel("htonl",
						(main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
								new CPrimitive(CPrimitives.UINT))),
				new FunctionModel("htons",
						(main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
								new CPrimitive(CPrimitives.USHORT))),
				new FunctionModel("ntohl",
						(main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
								new CPrimitive(CPrimitives.UINT))),
				new FunctionModel("ntohs",
						(main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
								new CPrimitive(CPrimitives.USHORT))),
				/** https://www.man7.org/linux/man-pages/man3/ffs.3.html **/
				new FunctionModel("ffs", (main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.INT)),
				new FunctionModel("ffsl",
						(main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.LONG)),
				new FunctionModel("ffsll",
						(main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.LONGLONG)));
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

	private Result handleSleep(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[0]));
		// Return a non-deterministic aux-var as an overapproximation
		// (since we cannot be sure, if the call was interrupted)
		final ICType retType = new CPrimitive(CPrimitives.UINT);
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, retType, AUXVAR.RETURNED);
		builder.addAuxVarWithDeclaration(auxVar).setLrValue(new RValue(auxVar.getExp(), retType));
		return builder.addOverapprox(new Overapprox(name, loc)).build();
	}

	private Result handleFfs(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name, final CPrimitives argPrimitive) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);
		final ExpressionResult argResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(argResult);

		final var resultType = new CPrimitive(CPrimitives.INT);
		final AuxVarInfo resultInfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, AUXVAR.RETURNED);
		builder.addAuxVarWithDeclaration(resultInfo);

		final int argSize = mTypeSizes.getSize(argPrimitive);
		final var argType = new CPrimitive(argPrimitive);

		// Get an expression for result that has the same type as the argument.
		final Expression resultExpr;
		if (argType.equals(resultType)) {
			resultExpr = resultInfo.getExp();
		} else {
			assert argSize >= mTypeSizes.getSize(resultType.getType()) : "expected argument larger than INT";
			final var convertedResult = mExpressionTranslation.convertIntToInt(loc,
					new ExpressionResult(new RValue(resultInfo.getExp(), resultType)), argType);
			builder.addAllExceptLrValue(convertedResult);
			resultExpr = convertedResult.getLrValue().getValue();
		}

		final var argZero = mExpressionTranslation.constructZero(loc, argType);
		final var argIsZero = mExpressionTranslation.constructBinaryEqualityExpression(loc,
				IASTBinaryExpression.op_equals, argResult.getLrValue().getValue(), argType, argZero, argType);

		final Statement[] caseZero, caseNonZero;
		{
			// Case "zero": argument is 0, and so is the return value
			final var resultZero = mExpressionTranslation.constructZero(loc, resultType);
			final var resultIsZero = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_equals, resultInfo.getExp(), resultType, resultZero, resultType);
			caseZero = new AssumeStatement[] { new AssumeStatement(loc, resultIsZero) };
		}
		{
			final ArrayList<Statement> statements = new ArrayList<>();

			// 1 <= result <= argSize*8
			final var one = mExpressionTranslation.constructLiteralForIntegerType(loc, argType, BigInteger.ONE);
			final long bitsPerByte = 8L;
			final var sizeExp = mExpressionTranslation.constructLiteralForIntegerType(loc, argType,
					BigInteger.valueOf(argSize * bitsPerByte));
			final var resultInRange = ExpressionFactory.and(loc,
					List.of(mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
							IASTBinaryExpression.op_lessEqual, one, argType, resultExpr, argType),
							mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
									IASTBinaryExpression.op_lessEqual, resultExpr, argType, sizeExp, argType)));
			statements.add(new AssumeStatement(loc, resultInRange));

			// expression "~0", which is 11...111 in binary.
			final var allOnes = mExpressionTranslation.constructUnaryExpression(loc, IASTUnaryExpression.op_tilde,
					argZero, argType);

			// 0 != arg & (1 << (result-1))
			// This means that at index "result", the argument has a 1.
			final var lShiftRes =
					mExpressionTranslation.handleBinaryBitwiseExpression(loc, IASTBinaryExpression.op_shiftLeft,
							mExpressionTranslation.constructLiteralForIntegerType(loc, argType, BigInteger.ONE),
							argType,
							mExpressionTranslation.constructArithmeticIntegerExpression(loc,
									IASTBinaryExpression.op_minus, resultExpr, argType, one, argType),
							argType, mAuxVarInfoBuilder);
			builder.addAllExceptLrValueAndStatements(lShiftRes);
			statements.addAll(lShiftRes.getStatements());
			final var andRes1 = mExpressionTranslation.handleBinaryBitwiseExpression(loc,
					IASTBinaryExpression.op_binaryAnd, argResult.getLrValue().getValue(), argType,
					lShiftRes.getLrValue().getValue(), argType, mAuxVarInfoBuilder);
			builder.addAllExceptLrValueAndStatements(andRes1);
			statements.addAll(andRes1.getStatements());
			final var resultBitIsSet = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_notequals, argZero, argType, andRes1.getLrValue().getValue(), argType);
			statements.add(new AssumeStatement(loc, resultBitIsSet));

			// 0 == arg & (~0 >> |arg|-(result-1))
			// This means that at all lower indices than "result", the argument has only zeroes.
			// We use the corresponding unsigned types to force a logical right-shift rather than an arithmetic shift.
			final var rShiftRes = mExpressionTranslation.handleBinaryBitwiseExpression(loc,
					IASTBinaryExpression.op_shiftRight, allOnes, mTypeSizes.getCorrespondingUnsignedType(argType),
					mExpressionTranslation.constructArithmeticIntegerExpression(loc, IASTBinaryExpression.op_minus,
							sizeExp, argType,
							mExpressionTranslation.constructArithmeticIntegerExpression(loc,
									IASTBinaryExpression.op_minus, resultExpr, argType, one, argType),
							argType),
					mTypeSizes.getCorrespondingUnsignedType(argType), mAuxVarInfoBuilder);
			builder.addAllExceptLrValueAndStatements(rShiftRes);
			statements.addAll(rShiftRes.getStatements());
			final var andRes2 = mExpressionTranslation.handleBinaryBitwiseExpression(loc,
					IASTBinaryExpression.op_binaryAnd, argResult.getLrValue().getValue(), argType,
					rShiftRes.getLrValue().getValue(), argType, mAuxVarInfoBuilder);
			builder.addAllExceptLrValueAndStatements(andRes2);
			statements.addAll(andRes2.getStatements());
			final var firstSetBit = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_equals, argZero, argType, andRes2.getLrValue().getValue(), argType);
			statements.add(new AssumeStatement(loc, firstSetBit));

			caseNonZero = statements.toArray(Statement[]::new);
		}

		builder.addStatement(new IfStatement(loc, argIsZero, caseZero, caseNonZero));
		builder.setLrValue(new LocalLValue(resultInfo.getLhs(), resultType, null));

		return builder.build();
	}
}
