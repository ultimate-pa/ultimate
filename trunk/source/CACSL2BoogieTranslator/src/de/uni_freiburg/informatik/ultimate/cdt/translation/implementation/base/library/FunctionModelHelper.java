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
import java.util.EnumSet;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.IMemoryPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryArea;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.CheckMessageProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;

/**
 * Helper class for implementations of {@link ILibraryModel}
 */
public class FunctionModelHelper {
	private final ExpressionTranslation mExpressionTranslation;
	private final MemoryHandler mMemoryHandler;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final TypeSizes mTypeSizes;
	private final ITypeHandler mTypeHandler;
	private final IMemoryPointer mMemoryPointer;
	private final boolean mCheckMemoryLeakInMain;
	private final boolean mSvcompMemtrackCompatibilityMode;

	public FunctionModelHelper(final AuxVarInfoBuilder auxVarInfoBuilder,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizes typeSizes, final ITypeHandler typeHandler, final boolean checkMemoryLeakInMain,
			final boolean svcompMemtrackCompatibilityMode, final IMemoryPointer memoryPointer) {
		mExpressionTranslation = expressionTranslation;
		mMemoryHandler = memoryHandler;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mCheckMemoryLeakInMain = checkMemoryLeakInMain;
		mSvcompMemtrackCompatibilityMode = svcompMemtrackCompatibilityMode;
		mMemoryPointer = memoryPointer;
	}

	/**
	 * Check if the expected number of arguments matches the actual size of {@code arguments} and throws an exception
	 * otherwise.
	 */
	public void checkArguments(final ILocation loc, final int expectedArgs, final String name,
			final IASTInitializerClause[] arguments) {
		if (arguments.length != expectedArgs) {
			throw new IncorrectSyntaxException(loc, name + " is expected to have " + expectedArgs
					+ " arguments, but was called with " + arguments.length);
		}
	}

	/**
	 * Handle a function call by dispatching all arguments with a non-deterministic return value (assumed to be in range
	 * of {@code resultType}) which is marked with the {@link Overapprox} annotation.
	 *
	 * @param main
	 *            the current dispatcher
	 * @param node
	 *            the function call expression
	 * @param loc
	 *            the location of the call
	 * @param methodName
	 *            the name of the method
	 * @param numberOfArgs
	 *            the number of arguments
	 * @param resultType
	 *            the return type
	 * @return An {@link ExpressionResult} representing the effect of the call
	 */
	public Result handleByOverapproximation(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String methodName, final int numberOfArgs, final ICType resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		for (final IASTInitializerClause argument : arguments) {
			builder.addAllExceptLrValue((ExpressionResult) main.dispatch(argument));
		}

		final ExpressionResult overapproxCall = constructOverapproximationForFunctionCall(loc, methodName, resultType);
		builder.addAllExceptLrValue(overapproxCall);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, overapproxCall.getLrValue().getValue(), resultType,
				builder);
		return builder.setLrValue(overapproxCall.getLrValue()).build();
	}

	/**
	 * Construct an auxiliary variable that will be use as a substitute for a function call. The result will be marked
	 * as an overapproximation. If you overapproximate a function call, don't forget to dispatch the function call's
	 * arguments: the arguments may have side effects.
	 *
	 * @param loc
	 *            a location
	 * @param functionName
	 *            the named of the function will be annotated to the overapproximation
	 * @param resultType
	 *            CType that determinies the type of the auxiliary variable
	 * @return An ExpressionResult that contains an overapproximated function call with the name functionName.
	 */
	public ExpressionResult constructOverapproximationForFunctionCall(final ILocation loc, final String functionName,
			final ICType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvar);
		builder.setLrValue(new RValue(auxvar.getExp(), resultType));
		return builder.addOverapprox(new Overapprox(functionName, loc)).build();
	}

	/**
	 * Overapproximate the reachability of unsupported functions by translating them to while(true) assert false; where
	 * the assert is labeled with an overapproximation
	 */
	public Result handleUnsupportedFunctionByOverapproximation(final IDispatcher main, final ILocation loc,
			final String name, final ICType returnType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addStatement(ExpressionTranslation.modelUnsupportedFeature(loc, name));
		if (!returnType.isVoidType()) {
			final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnType, AUXVAR.NONDET);
			builder.addAuxVarWithDeclaration(auxVar);
			builder.setLrValue(new RValue(auxVar.getExp(), returnType));
		}
		return builder.build();
	}

	/**
	 * We handle a function call by dispatching all arguments, but we then ignore the call completely.
	 *
	 * Useful for void functions that do nothing.
	 */
	public Result handleVoidFunctionBySkipAndDispatch(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String methodName, final int numberOfArgs) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			results.add((ExpressionResult) main.dispatch(argument));
		}
		return new ExpressionResultBuilder().addAllExceptLrValue(results).build();
	}

	/**
	 * Create an assertion or assumption statement annotated with a {@link Check} annotation.
	 *
	 * @param loc
	 *            location of the assertion or assumption node.
	 * @param functionName
	 *            name of the function for the assertion statement and {@link Check} annotation.
	 * @param checkProperty
	 *            enables creation of an assertion to check {@code expr}, otherwise an assumption is made.
	 * @param spec
	 *            type of {@link Check} for assertion or assumption statement annotation.
	 * @param expr
	 *            expression for assertion or assumption statement.
	 * @return {@link Statement} annotated with a {@link Check} annotation.
	 *
	 * @see {@link #createAnnotatedAssertOrAssume(ILocation, String, boolean, Spec, Expression, String)}
	 */
	public Statement createAnnotatedAssertOrAssume(final ILocation loc, final String functionName,
			final boolean checkProperty, final Spec spec, final Expression expr) {
		return createAnnotatedAssertOrAssume(loc, functionName, checkProperty, spec, expr, null);
	}

	/**
	 * Create an assertion or assumption statement annotated with a {@link Check} annotation.
	 *
	 * Create an {@code assert expr} or {@code assume expr} depending on the settings. If {@code checkProperty} is
	 * {@code true} (i.e. the check is enabled), an {@code assert expr} will be generated, otherwise an
	 * {@code assume expr} will be generated.
	 *
	 * @param loc
	 *            location of the assertion or assumption node.
	 * @param functionName
	 *            name of the function for the assertion statement and {@link Check} annotation.
	 * @param checkProperty
	 *            enables creation of an assertion to check {@code expr}, otherwise an assumption is made.
	 * @param spec
	 *            type of {@link Check} for assertion or assumption statement annotation.
	 * @param expr
	 *            expression for assertion or assumption statement.
	 * @param errorMsg
	 *            error message for a negative check result of an assertion.
	 *
	 * @return {@link Statement} annotated with a {@link Check} annotation.
	 */
	public Statement createAnnotatedAssertOrAssume(final ILocation loc, final String functionName,
			final boolean checkProperty, final Spec spec, final Expression expr, final String errorMsg) {
		final boolean checkMemoryleakInMain = mCheckMemoryLeakInMain
				&& mMemoryHandler.getRequiredMemoryStructureFeatures().isMemoryStructureInfrastructureRequired();
		if (!checkProperty && !checkMemoryleakInMain) {
			return new AssumeStatement(loc, expr);
		}

		// TODO 2017-11-26 Matthias: Workaround for memcleanup property.
		// Rationale: If we reach the SV-COMP error function (which has
		// is similar to the abort function) memory was not deallocated.
		// Proper solution: Check #valid array for all functions that
		// do not return (e.g., also abort and exit). Depending on the
		// discussion about the exact meaning of valid-memcleanup we
		// need separate arrays for stack and heap.
		// https://github.com/sosy-lab/sv-benchmarks/pull/1001
		final Check check;
		if (checkProperty) {
			final CheckMessageProvider msgProvider = new CheckMessageProvider();

			/* customize result message for error function specifications with function name */
			msgProvider.registerSpecificationErrorFunctionName(functionName);
			/* customize result message for specifications with error messages */
			msgProvider.registerSpecificationErrorMessage(spec, errorMsg);

			if (checkMemoryleakInMain) {
				check = new Check(EnumSet.of(spec, Spec.MEMORY_NEUTRAL), msgProvider);
			} else {
				check = new Check(spec, msgProvider);
			}
		} else {
			check = new Check(EnumSet.of(Spec.MEMORY_NEUTRAL));
		}
		final Statement st = new AssertStatement(loc, new NamedAttribute[] { new NamedAttribute(loc, "reach",
				new Expression[] { new StringLiteral(loc, check.toString()), new StringLiteral(loc, functionName) }) },
				expr);
		check.annotate(st);
		if (checkMemoryleakInMain && mSvcompMemtrackCompatibilityMode) {
			new Overapprox("memtrack", loc).annotate(st);
		}
		return st;
	}

	/**
	 * Checks if the given expression is a string literal.
	 *
	 * @param expr
	 *            An expression
	 * @return true iff expr is a string literal
	 */
	public boolean isStringLiteral(final IASTInitializerClause expr) {
		return expr instanceof IASTLiteralExpression
				&& ((IASTLiteralExpression) expr).getKind() == IASTLiteralExpression.lk_string_literal;
	}

	/**
	 * Get a non-deterministic string.
	 *
	 * @param loc
	 *            A location
	 * @return A model of a non-deterministic string or null (at the given location).
	 */
	public ExpressionResult getNondetStringOrNull(final ILocation loc) {
		final var charType = new CPrimitive(CPrimitives.CHAR);
		final var sizeT = mTypeSizes.getSizeT();
		final var resultType = new CPointer(charType);
		final var builder = new ExpressionResultBuilder();

		final AuxVarInfo retvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(retvar);
		builder.setLrValue(new LocalLValue(retvar.getLhs(), resultType, null));

		final var nullPtr =
				mMemoryPointer.constructNullPointer(loc, mExpressionTranslation.getCTypeOfPointerComponents());

		// one possible return value: NULL
		final var setPtrToNull = StatementFactory.constructSingleAssignmentStatement(loc, retvar.getLhs(), nullPtr);

		// alternative option: return a nondeterministic string of nondeterministic length
		final AuxVarInfo len = mAuxVarInfoBuilder.constructAuxVarInfo(loc, sizeT, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(len);

		// allocate memory for a string and end it with a null-char as terminator
		final var body = new ArrayList<Statement>();
		body.add(new HavocStatement(loc, new VariableLHS[] { len.getLhs() }));
		body.add(new AssumeStatement(loc,
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_greaterThan,
						len.getExp(), sizeT, mTypeSizes.constructLiteralForIntegerType(loc, sizeT, BigInteger.ZERO),
						sizeT)));
		body.add(mMemoryHandler.getUltimateMemAllocCall(len.getExp(), retvar.getLhs(), loc, MemoryArea.HEAP));

		final var nullChar = mTypeSizes.constructLiteralForIntegerType(loc, charType, BigInteger.ZERO);

		// *(retvar + (len - 1)) = '\0';
		{
			final var lenMinusOne = mExpressionTranslation.constructArithmeticIntegerExpression(loc,
					IASTBinaryExpression.op_minus, mExpressionTranslation.applyWraparound(loc, sizeT, len.getExp()),
					sizeT, mTypeSizes.constructLiteralForIntegerType(loc, sizeT, BigInteger.ONE), sizeT);
			final Expression lastChar = mMemoryHandler.addExpressionToPointer(loc, retvar.getExp(), lenMinusOne);
			body.addAll(mMemoryHandler.getWriteCall(loc,
					LRValueFactory.constructHeapLValue(mTypeHandler, lastChar, charType, null), nullChar, charType,
					false));
		}

		final var stmt = StatementFactory.constructIfStatement(loc, new WildcardExpression(loc),
				new Statement[] { setPtrToNull }, body.toArray(Statement[]::new));
		builder.addStatement(stmt);

		return builder.build();
	}

	public ExpressionResult constructIntegerLiteral(final ILocation loc, final BigInteger value,
			final CPrimitive type) {
		return new ExpressionResult(
				new RValue(mExpressionTranslation.constructLiteralForIntegerType(loc, type, value), type));
	}
}
