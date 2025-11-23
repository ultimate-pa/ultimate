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
import java.util.regex.Pattern;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion.StructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Model of functions performing input and output from stdio.h (C11 7.21, https://en.cppreference.com/w/c/header/stdio).
 * We cannot translate input and output properly in Boogie, therefore we either abstract or overapproximate most of
 * these functions.
 */
public class StdioLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final ExpressionTranslation mExpressionTranslation;
	private final TypeSizes mTypeSizes;
	private final MemoryHandler mMemoryHandler;
	private final DataRaceChecker mDataRaceChecker;
	private final ITypeHandler mTypeHandler;

	public StdioLibraryModel(final FunctionModelHelper helper, final ExpressionResultTransformer exprResultTransformer,
			final AuxVarInfoBuilder auxVarInfoBuilder, final ExpressionTranslation expressionTranslation,
			final TypeSizes typeSizes, final MemoryHandler memoryHandler, final DataRaceChecker dataRaceChecker,
			final ITypeHandler typeHandler) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mExpressionTranslation = expressionTranslation;
		mTypeSizes = typeSizes;
		mMemoryHandler = memoryHandler;
		mDataRaceChecker = dataRaceChecker;
		mTypeHandler = typeHandler;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		result.add(new FunctionModel("printf", (main, node, loc, name) -> handlePrintF(main, node, loc)));

		// https://en.cppreference.com/w/c/io/fgets
		result.add(new FunctionModel("fgets", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPointer(new CPrimitive(CPrimitives.CHAR)))));

		// https://en.cppreference.com/w/c/io/fgetc
		result.add(new FunctionModel("fgetc", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.INT))));

		// TODO 20211105 Matthias: Unsound because our implementation of printf is
		// unsound and because we consider wchars as chars.
		result.add(new FunctionModel("wprintf", (main, node, loc, name) -> handlePrintF(main, node, loc)));
		result.add(new FunctionModel("fprintf", (main, node, loc, name) -> handlePrintFunction(main, node, loc)));
		result.add(new FunctionModel("sprintf", (main, node, loc, name) -> handleSPrintF(main, node, loc)));
		result.add(new FunctionModel("snprintf", this::handleSnPrintF));
		result.add(new FunctionModel("swprintf", this::handleSnPrintF));

		// https://en.cppreference.com/w/c/io/fscanf
		result.add(new FunctionModel("scanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 1)));
		result.add(new FunctionModel("scanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 1)));
		result.add(new FunctionModel("fscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2)));
		result.add(new FunctionModel("fscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2)));
		result.add(new FunctionModel("sscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2)));
		result.add(new FunctionModel("sscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2)));

		// https://en.cppreference.com/w/c/io/fwscanf
		result.add(new FunctionModel("wscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 1)));
		result.add(new FunctionModel("wscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 1)));
		result.add(new FunctionModel("fwscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2)));
		result.add(new FunctionModel("fwscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2)));
		result.add(new FunctionModel("swscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2)));
		result.add(new FunctionModel("swscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2)));

		// https://en.cppreference.com/w/c/io/puts
		result.add(new FunctionModel("puts", this::handlePuts));

		/**
		 * 7.21.3 Files
		 *
		 * We cannot handle files properly, therefore we just overapproximate. For functions that modify the files, we
		 * use the "assert false" overapproximation, otherwise we just overapproximate the return value.
		 */
		result.add(new FunctionModel("fflush", (main, node, loc, name) -> mHelper
				.handleUnsupportedFunctionByOverapproximation(main, loc, name, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("fopen", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 2, CPointer.voidPointer())));
		result.add(new FunctionModel("fclose", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("feof", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("fseek", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("fread", (main, node, loc, name) -> mHelper
				.handleUnsupportedFunctionByOverapproximation(main, loc, name, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("ferror", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("fputs", (main, node, loc, name) -> mHelper
				.handleUnsupportedFunctionByOverapproximation(main, loc, name, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("fwrite", (main, node, loc, name) -> mHelper
				.handleUnsupportedFunctionByOverapproximation(main, loc, name, new CPrimitive(CPrimitives.ULONGLONG))));
		result.add(new FunctionModel("setbuf", (main, node, loc, name) -> mHelper
				.handleUnsupportedFunctionByOverapproximation(main, loc, name, new CPrimitive(CPrimitives.VOID))));
		// https://en.cppreference.com/w/c/io/clearerr
		// We don't handle the error flags anyway, so we just dispatch the argument.
		result.add(new FunctionModel("clearerr",
				(main, node, loc, name) -> mHelper.handleVoidFunctionBySkipAndDispatch(main, node, loc, name, 1)));

		return result;

	}

	// Overapproximates sprintf as follows:
	// ctr:=0; while (*) { havoc aux; *(ptr+ctr) := aux; ctr := ctr + 1; }
	private Result handleSPrintF(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		final IASTInitializerClause[] arguments = node.getArguments();
		assert arguments.length >= 1 : "insufficient arguments to snprintf";
		final var builder = new ExpressionResultBuilder();

		final Overapprox overAppFlag = new Overapprox("snprintf", loc);
		builder.addOverapprox(overAppFlag);

		// first argument is ptr
		final var ptr = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		builder.addAllExceptLrValue(ptr);

		// dispatch remaining arguments (except for string literals)
		for (int i = 1; i < arguments.length; ++i) {
			if (mHelper.isStringLiteral(arguments[i])) {
				continue;
			}
			final ExpressionResult argRes =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[i]);
			builder.addAllExceptLrValue(argRes);
		}

		// declare loop counter ctr
		final AuxVarInfo ctr = mAuxVarInfoBuilder.constructAuxVarInfo(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), SFO.AUXVAR.LOOPCTR);
		builder.addAuxVarWithDeclaration(ctr);

		// declare nondet aux var
		final AuxVarInfo auxvar =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.CHAR), SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvar);

		// ctr := 0
		final var zero = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final var initCtr = StatementFactory.constructSingleAssignmentStatement(loc, ctr.getLhs(), zero);
		builder.addStatement(initCtr);

		final var body = new ArrayList<Statement>();

		// havoc aux;
		final var havocNondet = new HavocStatement(loc, new VariableLHS[] { auxvar.getLhs() });
		body.add(havocNondet);

		// *(ptr + ctr) := aux

		final var ptrPlusCtr = mMemoryHandler.addExpressionToPointer(loc, ptr.getLrValue().getValue(), ctr.getExp());

		final var ptrPlusCtrHlv = LRValueFactory.constructHeapLValue(mTypeHandler, ptrPlusCtr, ptr.getCType(), null);
		final var writeToMem = mMemoryHandler.getWriteCall(loc, ptrPlusCtrHlv, auxvar.getExp(),
				new CPrimitive(CPrimitives.CHAR), false);
		for (final var write : writeToMem) {
			overAppFlag.annotate(write);
		}
		body.addAll(writeToMem);
		if (mDataRaceChecker != null) {
			mDataRaceChecker.checkOnWrite(builder, loc, ptrPlusCtrHlv);
		}

		// ctr := ctr + 1
		final var incrementCtr = StatementFactory.constructSingleAssignmentStatement(loc, ctr.getLhs(),
				mExpressionTranslation.constructArithmeticIntegerExpression(loc, IASTBinaryExpression.op_plus,
						ctr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents(),
						mTypeSizes.constructLiteralForIntegerType(loc,
								mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE),
						mExpressionTranslation.getCTypeOfPointerComponents()));
		body.add(incrementCtr);

		final var loop = new WhileStatement(loc, new WildcardExpression(loc), new LoopInvariantSpecification[0],
				body.toArray(Statement[]::new));
		builder.addStatement(loop);

		final var ret =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.CHAR), SFO.AUXVAR.RETURNED);
		builder.addAuxVarWithDeclaration(ret);
		builder.setLrValue(new LocalLValue(ret.getLhs(), new CPrimitive(CPrimitives.CHAR), null));

		return builder.build();
	}

	// Overapproximates snprintf as follows:
	// ctr:=0; while (*) { assume ctr < len; havoc aux; *(ptr+ctr) := aux; ctr := ctr + 1; }
	private Result handleSnPrintF(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		assert arguments.length >= 2 : "insufficient arguments to snprintf";
		final var builder = new ExpressionResultBuilder();

		final Overapprox overAppFlag = new Overapprox(name, loc);
		builder.addOverapprox(overAppFlag);

		// first argument is ptr
		final var ptr = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		builder.addAllExceptLrValue(ptr);

		// second argument is len
		final var len = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc, arguments[1],
				mExpressionTranslation.getCTypeOfPointerComponents());
		builder.addAllExceptLrValue(len);

		// dispatch remaining arguments (except for string literals)
		for (int i = 2; i < arguments.length; ++i) {
			if (mHelper.isStringLiteral(arguments[i])) {
				continue;
			}
			final ExpressionResult argRes =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[i]);
			builder.addAllExceptLrValue(argRes);
		}

		// declare loop counter ctr
		final AuxVarInfo ctr = mAuxVarInfoBuilder.constructAuxVarInfo(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), SFO.AUXVAR.LOOPCTR);
		builder.addAuxVarWithDeclaration(ctr);

		// declare nondet aux var
		final AuxVarInfo auxvar =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.CHAR), SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvar);

		// ctr := 0
		final var zero = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final var initCtr = StatementFactory.constructSingleAssignmentStatement(loc, ctr.getLhs(), zero);
		builder.addStatement(initCtr);

		final var body = new ArrayList<Statement>();

		// assume ctr < len;
		final var assumeInRange = new AssumeStatement(loc,
				mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_lessThan,
						ctr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents(), len.getLrValue().getValue(),
						mExpressionTranslation.getCTypeOfPointerComponents()));
		body.add(assumeInRange);

		// havoc aux;
		final var havocNondet = new HavocStatement(loc, new VariableLHS[] { auxvar.getLhs() });
		body.add(havocNondet);

		// *(ptr + ctr) := aux
		final Expression ptrPlusCtr =
				mMemoryHandler.addExpressionToPointer(loc, ptr.getLrValue().getValue(), ctr.getExp());

		final var ptrPlusCtrHlv = LRValueFactory.constructHeapLValue(mTypeHandler, ptrPlusCtr, ptr.getCType(), null);
		final var writeToMem = mMemoryHandler.getWriteCall(loc, ptrPlusCtrHlv, auxvar.getExp(),
				new CPrimitive(CPrimitives.CHAR), false);
		for (final var write : writeToMem) {
			overAppFlag.annotate(write);
		}
		body.addAll(writeToMem);
		if (mDataRaceChecker != null) {
			mDataRaceChecker.checkOnWrite(builder, loc, ptrPlusCtrHlv);
		}

		// ctr := ctr + 1
		final var incrementCtr = StatementFactory.constructSingleAssignmentStatement(loc, ctr.getLhs(),
				mExpressionTranslation.constructArithmeticIntegerExpression(loc, IASTBinaryExpression.op_plus,
						ctr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents(),
						mTypeSizes.constructLiteralForIntegerType(loc,
								mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE),
						mExpressionTranslation.getCTypeOfPointerComponents()));
		body.add(incrementCtr);

		final var loop = new WhileStatement(loc, new WildcardExpression(loc), new LoopInvariantSpecification[0],
				body.toArray(Statement[]::new));
		builder.addStatement(loop);

		final var ret =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.CHAR), SFO.AUXVAR.RETURNED);
		builder.addAuxVarWithDeclaration(ret);
		builder.setLrValue(new LocalLValue(ret.getLhs(), new CPrimitive(CPrimitives.CHAR), null));

		return builder.build();
	}

	/**
	 * Handles all derivates of *scanf as an overapproximation by writing non-deterministic values to all arguments
	 * starting from {@code firstArgumentToWrite}.
	 */
	// TODO Frank 2022-11-14: In general this is unsound since scanf can write multiple bytes. E.g. for the format %2c
	// we would need two writes, for the format %s even non-determinstically many writes! Determining whether this
	// occurs in the format, is only possible if the format is a literal (it can be any expression in general).
	private Result handleScanf(final String name, final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final int firstArgumentToWrite) {
		// The application is only marked as an overapproximation, if we read from a string.
		final boolean markAsOverapproximation = name.startsWith("sscanf") || name.startsWith("swscanf");
		final IASTInitializerClause[] arguments = node.getArguments();
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		for (int i = 0; i < arguments.length; i++) {
			if (i == firstArgumentToWrite - 1 && mHelper.isStringLiteral(arguments[i])) {
				final String format = arguments[i].toString();
				// WORKAROUND for #761: We always report unknown, whenever %s, %2c, ... occurs in the pattern.
				if (Pattern.matches(".*?%(s|\\d+c).*", format)) {
					return mHelper.handleUnsupportedFunctionByOverapproximation(main, loc, name,
							new CPrimitive(CPrimitives.LONG));
				}
			}
			if (i < firstArgumentToWrite) {
				// Don't dispatch string literals
				if (!mHelper.isStringLiteral(arguments[i])) {
					builder.addAllExceptLrValue(
							mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[i]));
				}
				continue;
			}

			final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[i]);
			builder.addAllExceptLrValue(pointer);
			// Write a non-deterministic value to the given address, but make sure the value is in range
			final ICType valueType = ((CPointer) pointer.getCType()).getPointsToType();
			final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, valueType, SFO.AUXVAR.NONDET);
			builder.addAuxVarWithDeclaration(auxvar);
			mExpressionTranslation.addAssumeValueInRangeStatements(loc, auxvar.getExp(), valueType, builder);
			final ExpressionResult writeResult =
					mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(), auxvar.getExp());
			if (markAsOverapproximation) {
				writeResult.getStatements().forEach(new Overapprox(name, loc)::annotate);
			}
			builder.addAllExceptLrValue(writeResult);
		}

		// The number of arguments to which sth should be written is returned.
		// Therefore we create a fresh variable and assume that it is in the desired range
		// (0 to the number of variables written to)
		final CPrimitive retValueType = new CPrimitive(CPrimitives.LONG);
		final AuxVarInfo returnAuxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, retValueType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(returnAuxVar);
		final var minValue = mExpressionTranslation.constructLiteralForIntegerType(loc, retValueType, BigInteger.ZERO);
		final var retVal = returnAuxVar.getExp();
		final var greaterMin = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, minValue, retValueType, retVal, retValueType);
		final int writtenArgs = arguments.length - firstArgumentToWrite;
		final var maxValue = mExpressionTranslation.constructLiteralForIntegerType(loc, retValueType,
				BigInteger.valueOf(writtenArgs));
		final var smallerMax = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, retVal, retValueType, maxValue, retValueType);
		builder.addStatement(new AssumeStatement(loc, ExpressionFactory.and(loc, List.of(greaterMin, smallerMax))));
		builder.setLrValue(new RValue(retVal, retValueType));
		if (markAsOverapproximation) {
			builder.addOverapprox(new Overapprox(name, loc));
		}

		return builder.build();
	}

	private ExpressionResult handlePrintFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		final AuxVarInfo auxvarinfo =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.INT), SFO.AUXVAR.RETURNED);
		resultBuilder.addAuxVarWithDeclaration(auxvarinfo);
		resultBuilder.addStatement(new HavocStatement(loc, new VariableLHS[] { auxvarinfo.getLhs() }));

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), new CPrimitive(CPrimitives.INT));
		resultBuilder.setLrValue(returnValue);

		// dispatch all arguments
		for (final IASTInitializerClause arg : node.getArguments()) {
			if (mHelper.isStringLiteral(arg)) {
				continue;
			}
			final ExpressionResult argRes =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arg);
			resultBuilder.addAllExceptLrValue(argRes);
		}

		return resultBuilder.build();
	}

	private Result handlePrintF(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		return handlePrintFunction(main, node, loc);
	}

	private Result handlePuts(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		mHelper.checkArguments(loc, 1, name, node.getArguments());
		return handlePrintFunction(main, node, loc);
	}

	private static ICType getFileType() {
		final var charPointer = new CPointer(new CPrimitive(CPrimitives.CHAR));
		final var intType = new CPrimitive(CPrimitives.INT);
		// We just chose the same definition as GCC for now
		return new CStructOrUnion(StructOrUnion.STRUCT, "FILE",
				List.of("_ptr", "_cnt", "_base", "_flag", "_file", "_charbuf", "_bufsiz", "_tmpfname"),
				List.of(charPointer, intType, charPointer, intType, intType, intType, intType, charPointer),
				List.of(-1, -1, -1, -1, -1, -1, -1, -1));
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		return List.of(new TypeModel("FILE", getFileType()));
	}
}
