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

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
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
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Modelling of various C functions from Linux, see https://man7.org/linux/man-pages/
 */
public class LinuxLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final TypeSizes mTypeSizes;
	private final ExpressionTranslation mExpressionTranslation;

	public LinuxLibraryModel(final FunctionModelHelper helper, final AuxVarInfoBuilder auxVarInfoBuilder,
			final ExpressionResultTransformer exprResultTransformer, final TypeSizes typeSizes,
			final ExpressionTranslation expressionTranslation) {
		mHelper = helper;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mExprResultTransformer = exprResultTransformer;
		mTypeSizes = typeSizes;
		mExpressionTranslation = expressionTranslation;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		return List.of(
				/** https://www.man7.org/linux/man-pages/man3/sleep.3.html **/
				new FunctionModel("sleep", this::handleSleep),
				/**
				 * https://man7.org/linux/man-pages/man3/htons.3p.html "htonl, htons, ntohl, ntohs - convert values
				 * between host and network byte order"
				 *
				 * We simply overapproximate those functions.
				 */
				new FunctionModel("htonl",
						(main, node, loc, name) -> mHelper.handleByOverapproximation(main, node, loc, name, 1,
								new CPrimitive(CPrimitives.UINT))),
				new FunctionModel("htons",
						(main, node, loc, name) -> mHelper.handleByOverapproximation(main, node, loc, name, 1,
								new CPrimitive(CPrimitives.USHORT))),
				new FunctionModel("ntohl",
						(main, node, loc, name) -> mHelper.handleByOverapproximation(main, node, loc, name, 1,
								new CPrimitive(CPrimitives.UINT))),
				new FunctionModel("ntohs",
						(main, node, loc, name) -> mHelper.handleByOverapproximation(main, node, loc, name, 1,
								new CPrimitive(CPrimitives.USHORT))),
				/** https://www.man7.org/linux/man-pages/man3/ffs.3.html **/
				new FunctionModel("ffs", (main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.INT)),
				new FunctionModel("ffsl",
						(main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.LONG)),
				new FunctionModel("ffsll",
						(main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.LONGLONG)));
	}

	private Result handleSleep(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
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
		mHelper.checkArguments(loc, 1, name, arguments);
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
