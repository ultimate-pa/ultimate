/*
 * Copyright (C) 2013-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LTLStepAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;

/**
 * The {@link StandardFunctionHandler} creates the translation for various functions where we have our own specification
 * or implementation. This is typically the case for functions defined in the C standard, but also for various standard
 * libraries or SV-COMP extensions.
 *
 * @author Markus Lindenmann,
 * @auhtor Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class StandardFunctionHandler {

	private static final int ARGS_COUNT_BUILTIN_MEMCPY = 3;

	private final Map<String, IFunctionModelHandler> mFunctionModels;

	private final ITypeHandler mTypeHandler;

	private final AExpressionTranslation mExpressionTranslation;

	private final MemoryHandler mMemoryHandler;

	private final StructHandler mStructHandler;

	private final TypeSizeAndOffsetComputer mTypeSizeComputer;

	private final FunctionHandler mFunctionHandler;

	private final CHandler mCHandler;

	public StandardFunctionHandler(final ITypeHandler typeHandler, final AExpressionTranslation expressionTranslation,
			final MemoryHandler memoryHandler, final StructHandler structHandler,
			final TypeSizeAndOffsetComputer typeSizeComputer, final FunctionHandler functionHandler,
			final CHandler cHandler) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = expressionTranslation;
		mMemoryHandler = memoryHandler;
		mStructHandler = structHandler;
		mTypeSizeComputer = typeSizeComputer;
		mFunctionHandler = functionHandler;
		mCHandler = cHandler;

		mFunctionModels = getFunctionModels();
	}

	/**
	 * Check if the given function has an "integrated" specification or implementation and return a {@link Result} that
	 * contains a translation of the function if this is the case.
	 *
	 * Return null otherwise.
	 *
	 * @param main
	 * @param node
	 * @param astIdExpression
	 * @return
	 */
	public Result translateStandardFunction(final Dispatcher main, final IASTFunctionCallExpression node,
			final IASTIdExpression astIdExpression) {
		assert node
				.getFunctionNameExpression() == astIdExpression : "astIdExpression is not the name of the called function";
		final String methodName = astIdExpression.getName().toString();
		final IFunctionModelHandler functionModel = mFunctionModels.get(methodName);
		if (functionModel != null) {
			final ILocation loc = main.getLocationFactory().createCLocation(node);
			return functionModel.handleFunction(main, node, loc, methodName);
		}
		return null;
	}

	private Map<String, IFunctionModelHandler> getFunctionModels() {
		final Map<String, IFunctionModelHandler> map = new HashMap<>();

		final IFunctionModelHandler skip = (main, node, loc, name) -> handleByIgnore(main, loc, name);
		final IFunctionModelHandler die = (main, node, loc, name) -> handleByUnsupportedSyntaxException(loc, name);

		map.put("pthread_create", die);
		map.put("sin", die);

		/*
		 * builtin_prefetch according to https://gcc.gnu.org/onlinedocs/gcc-3.4.5/gcc/Other-Builtins.html (state:
		 * 5.6.2015) triggers the processor to load something into cache, does nothing else is void thus has no return
		 * value
		 */
		map.put("__builtin_prefetch", skip);
		map.put("__builtin_va_start", skip);
		map.put("__builtin_va_end", skip);

		map.put("__builtin_expect", (main, node, loc, name) -> handleBuiltinExpect(main, node));
		map.put("__builtin_object_size", (main, node, loc, name) -> handleBuiltinObjectSize(main, loc));

		map.put("abort", (main, node, loc, name) -> handleAbort(loc));

		map.put("printf", (main, node, loc, name) -> handlePrintF(main, node, loc));

		map.put("__builtin_memcpy", (main, node, loc, name) -> handleMemCopy(main, node, loc));
		map.put("memcpy", (main, node, loc, name) -> handleMemCopy(main, node, loc));

		// various float builtins
		map.put("nan", (main, node, loc, name) -> handleNaN(loc, name));
		map.put("nanf", (main, node, loc, name) -> handleNaN(loc, name));
		map.put("nanl", (main, node, loc, name) -> handleNaN(loc, name));
		map.put("__builtin_nan", (main, node, loc, name) -> handleNaN(loc, "nan"));
		map.put("__builtin_nanf", (main, node, loc, name) -> handleNaN(loc, "nanf"));
		map.put("__builtin_nanl", (main, node, loc, name) -> handleNaN(loc, "nanl"));
		map.put("__builtin_inff", (main, node, loc, name) -> handleNaN(loc, "inff"));
		map.put("__builtin_isgreater", (main, node, loc, name) -> handleBuiltinBinaryFloatComparison(main, node, loc,
				IASTBinaryExpression.op_greaterThan));
		map.put("__builtin_isgreaterequal", (main, node, loc, name) -> handleBuiltinBinaryFloatComparison(main, node,
				loc, IASTBinaryExpression.op_greaterEqual));
		map.put("__builtin_isless", (main, node, loc, name) -> handleBuiltinBinaryFloatComparison(main, node, loc,
				IASTBinaryExpression.op_lessThan));
		map.put("__builtin_islessequal", (main, node, loc, name) -> handleBuiltinBinaryFloatComparison(main, node, loc,
				IASTBinaryExpression.op_lessEqual));
		map.put("__builtin_isunordered", (main, node, loc, name) -> handleBuiltinIsUnordered(main, node, loc));
		map.put("__builtin_islessgreater", (main, node, loc, name) -> handleBuiltinIsLessGreater(main, node, loc));

		map.put("__VERIFIER_ltl_step", (main, node, loc, name) -> handleLtlStep(main, node, loc));
		map.put("__VERIFIER_error", (main, node, loc, name) -> handleErrorFunction(main, node, loc));
		map.put("__VERIFIER_assume", (main, node, loc, name) -> handleVerifierAssume(main, node, loc));

		map.put("__VERIFIER_nondet_bool",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.BOOL)));
		map.put("__VERIFIER_nondet__Bool",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.BOOL)));
		map.put("__VERIFIER_nondet_char",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.CHAR)));
		map.put("__VERIFIER_nondet_pchar",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.CHAR)));
		map.put("__VERIFIER_nondet_float",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.FLOAT)));
		map.put("__VERIFIER_nondet_double",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.DOUBLE)));
		map.put("__VERIFIER_nondet_size_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT)));
		map.put("__VERIFIER_nondet_int",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT)));
		map.put("__VERIFIER_nondet_long",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG)));
		map.put("__VERIFIER_nondet_loff_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG)));
		map.put("__VERIFIER_nondet_short",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.SHORT)));
		map.put("__VERIFIER_nondet_pointer", (main, node, loc, name) -> handleVerifierNonDet(main, loc,
				new CPointer(new CPrimitive(CPrimitives.VOID))));
		map.put("__VERIFIER_nondet_uchar",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UCHAR)));
		map.put("__VERIFIER_nondet_unsigned",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT)));
		map.put("__VERIFIER_nondet_uint",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT)));
		map.put("__VERIFIER_nondet_ulong",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONG)));
		map.put("__VERIFIER_nondet_ushort",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.USHORT)));

		return Collections.unmodifiableMap(map);
	}

	private static Result handleBuiltinExpect(final Dispatcher main, final IASTFunctionCallExpression node) {
		// this is a gcc-builtin function that helps with branch prediction, it always returns the first argument.
		return main.dispatch(node.getArguments()[0]);
	}

	private static ExpressionResult handleAbort(final ILocation loc) {
		return new ExpressionResult(Collections.singletonList(new AssumeStatement(loc, new BooleanLiteral(loc, false))),
				null);
	}

	private Result handleVerifierNonDet(final Dispatcher main, final ILocation loc, final CType cType) {
		final List<Statement> stmt = new ArrayList<>();
		final List<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ASTType type = mTypeHandler.cType2AstType(loc, cType);
		final String tmpName = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, cType);
		final VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpName, type, loc);
		decl.add(tVarDecl);
		auxVars.put(tVarDecl, loc);

		final LRValue returnValue = new RValue(new IdentifierExpression(loc, tmpName), cType);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(),
				stmt);

		assert CHandler.isAuxVarMapComplete(main.mNameHandler, decl, auxVars);
		return new ExpressionResult(stmt, returnValue, decl, auxVars);
	}

	private Result handleVerifierAssume(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final List<Expression> args = new ArrayList<>();
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause inParam : node.getArguments()) {
			final ExpressionResult in = ((ExpressionResult) main.dispatch(inParam)).switchToRValueIfNecessary(main,
					mMemoryHandler, mStructHandler, loc);
			if (in.mLrVal.getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}
			in.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
			args.add(in.getLrValue().getValue());
			results.add(in);
		}
		// according to SV-Comp specification!
		assert args.size() == 1;
		final ExpressionResult rtr = combineExpressionResults(null, results);
		for (final Expression a : args) {
			// could just take the first as there is only one, but it's so easy to make it more general..
			rtr.addStatement(new AssumeStatement(loc, a));
		}
		assert CHandler.isAuxVarMapComplete(main.mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleNaN(final ILocation loc, final String methodName) {
		return mExpressionTranslation.createNanOrInfinity(loc, methodName);
	}

	private Result handleBuiltinBinaryFloatComparison(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final int op) {

		/*
		 * Handle the following float comparisons
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isless
		 *
		 * http://en.cppreference.com/w/c/numeric/math/islessequal
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isgreater
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isgreaterequal
		 *
		 */

		if (node.getArguments().length != 2) {
			throw new IncorrectSyntaxException(loc,
					"Function has only two arguments, but was called with " + node.getArguments().length);
		}

		final ExpressionResult leftResult = (ExpressionResult) main.dispatch(node.getArguments()[0]);
		final ExpressionResult rightResult = (ExpressionResult) main.dispatch(node.getArguments()[1]);

		final ExpressionResult rl = leftResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		final ExpressionResult rr = rightResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);

		// Note: this works because SMTLIB already ensures that all comparisons return false if one of the arguments is
		// NaN

		return mCHandler.handleRelationalOperators(main, loc, op, rl, rr);
	}

	private Result handleBuiltinIsUnordered(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		/*
		 * http://en.cppreference.com/w/c/numeric/math/isunordered
		 *
		 * int isunordered (real-floating x, real-floating y)
		 *
		 * This macro determines whether its arguments are unordered. In other words, it is true if x or y are NaN, and
		 * false otherwise.
		 *
		 */
		if (node.getArguments().length != 2) {
			throw new IncorrectSyntaxException(loc,
					"Function has only two arguments, but was called with " + node.getArguments().length);
		}
		final ExpressionResult leftResult = (ExpressionResult) main.dispatch(node.getArguments()[0]);
		final ExpressionResult rightResult = (ExpressionResult) main.dispatch(node.getArguments()[1]);
		final ExpressionResult leftRvaluedResult =
				leftResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		final ExpressionResult rightRvaluedResult =
				rightResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		final ExpressionResult nanLResult = mExpressionTranslation.createNanOrInfinity(loc, "NAN");
		final ExpressionResult nanRResult = mExpressionTranslation.createNanOrInfinity(loc, "NAN");

		mExpressionTranslation.usualArithmeticConversions(loc, nanLResult, leftRvaluedResult);
		final BinaryExpression leftExpr = new BinaryExpression(loc, Operator.COMPEQ, leftResult.getLrValue().getValue(),
				nanLResult.getLrValue().getValue());

		mExpressionTranslation.usualArithmeticConversions(loc, nanRResult, rightRvaluedResult);
		final BinaryExpression rightExpr = new BinaryExpression(loc, Operator.COMPEQ,
				rightResult.getLrValue().getValue(), nanRResult.getLrValue().getValue());
		final BinaryExpression expr = new BinaryExpression(loc, Operator.LOGICOR, leftExpr, rightExpr);
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr =
				combineExpressionResults(lrVal, leftRvaluedResult, rightRvaluedResult, nanLResult, nanRResult);
		assert CHandler.isAuxVarMapComplete(main.mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleBuiltinIsLessGreater(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		/*
		 * http://en.cppreference.com/w/c/numeric/math/islessgreater
		 *
		 * int islessgreater (real-floating x, real-floating y)
		 *
		 * This macro determines whether the argument x is less or greater than y.
		 *
		 * It is equivalent to (x) < (y) || (x) > (y) (although it only evaluates x and y once), but no exception is
		 * raised if x or y are NaN.
		 *
		 * This macro is not equivalent to x != y, because that expression is true if x or y are NaN.
		 *
		 * Note: I did not find any reference as to how often x and y are evaluated; it seems this can actually evaluate
		 * x and y twice.
		 */
		if (node.getArguments().length != 2) {
			throw new IncorrectSyntaxException(loc,
					"Function has only two arguments, but was called with " + node.getArguments().length);
		}

		final ExpressionResult leftResult = (ExpressionResult) main.dispatch(node.getArguments()[0]);
		final ExpressionResult rightResult = (ExpressionResult) main.dispatch(node.getArguments()[1]);

		final ExpressionResult leftRvaluedResult =
				leftResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		final ExpressionResult rightRvaluedResult =
				rightResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		mExpressionTranslation.usualArithmeticConversions(loc, leftRvaluedResult, rightRvaluedResult);

		final ExpressionResult lessThan = mCHandler.handleRelationalOperators(main, loc,
				IASTBinaryExpression.op_lessThan, leftRvaluedResult, rightRvaluedResult);
		final ExpressionResult greaterThan = mCHandler.handleRelationalOperators(main, loc,
				IASTBinaryExpression.op_greaterThan, leftRvaluedResult, rightRvaluedResult);

		final BinaryExpression expr = new BinaryExpression(loc, Operator.LOGICOR, lessThan.getLrValue().getValue(),
				greaterThan.getLrValue().getValue());
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr = combineExpressionResults(lrVal, lessThan, greaterThan);
		assert CHandler.isAuxVarMapComplete(main.mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleBuiltinObjectSize(final Dispatcher main, final ILocation loc) {
		main.warn(loc, "used trivial implementation of __builtin_object_size");
		final CPrimitive cType = new CPrimitive(CPrimitives.INT);
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO);
		return new ExpressionResult(new RValue(zero, cType));
	}

	private Result handlePrintF(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		// skip if parent of parent is CompoundStatement
		// otherwise, replace by havoced variable
		if (node.getParent().getParent() instanceof IASTCompoundStatement) {
			return new SkipResult();
		}

		final List<Statement> stmt = new ArrayList<>();
		final List<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final List<Overapprox> overappr = new ArrayList<>();

		// 2015-11-05 Matthias: TODO check if int is reasonable here
		final ASTType tempType = mTypeHandler.cType2AstType(loc, new CPrimitive(CPrimitives.INT));
		final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, null);
		final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { tId }, tempType) });
		auxVars.put(tVarDecl, loc);
		decl.add(tVarDecl);
		stmt.add(new HavocStatement(loc, new VariableLHS[] { new VariableLHS(loc, tId) }));
		final LRValue returnValue = new RValue(new IdentifierExpression(loc, tId), null);
		assert CHandler.isAuxVarMapComplete(main.mNameHandler, decl, auxVars);
		return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
	}

	private Result handleMemCopy(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		assert node.getArguments().length == ARGS_COUNT_BUILTIN_MEMCPY : "wrong number of arguments";
		ExpressionResult dest = (ExpressionResult) handleBuiltinExpect(main, node);
		dest = dest.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		main.mCHandler.convert(loc, dest, new CPointer(new CPrimitive(CPrimitives.VOID)));
		ExpressionResult src = (ExpressionResult) main.dispatch(node.getArguments()[1]);
		src = src.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		main.mCHandler.convert(loc, src, new CPointer(new CPrimitive(CPrimitives.VOID)));
		ExpressionResult size = (ExpressionResult) main.dispatch(node.getArguments()[2]);
		size = size.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		main.mCHandler.convert(loc, size, mTypeSizeComputer.getSizeT());

		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(dest, src, size);

		final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MEMCPYRES, dest.mLrVal.getCType());
		final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { tId }, main.mTypeHandler.constructPointerType(loc)) });
		result.mDecl.add(tVarDecl);
		result.mAuxVars.put(tVarDecl, loc);

		final Statement call = mMemoryHandler.constructMemcpyCall(loc, dest.mLrVal.getValue(), src.mLrVal.getValue(),
				size.mLrVal.getValue(), tId);
		result.mStmt.add(call);
		result.mLrVal = new RValue(new IdentifierExpression(loc, tId), new CPointer(new CPrimitive(CPrimitives.VOID)));

		// add required information to function handler.
		mFunctionHandler.addCallGraphNode(MemoryModelDeclarations.C_Memcpy.getName());
		mFunctionHandler.addCallGraphEdge(mFunctionHandler.getCurrentProcedureID(),
				MemoryModelDeclarations.C_Memcpy.getName());
		mFunctionHandler.addModifiedGlobalEntry(MemoryModelDeclarations.C_Memcpy.getName());

		return result;
	}

	private static Result handleErrorFunction(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final boolean checkSvcompErrorfunction =
				main.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SVCOMP_ERRORFUNCTION);
		final Expression falseLiteral = new BooleanLiteral(loc, new InferredType(Type.Boolean), false);
		Statement st;
		if (checkSvcompErrorfunction) {
			final Check check = new Check(Spec.ERROR_FUNCTION);
			st = new AssertStatement(loc, falseLiteral);
			check.annotate(st);
		} else {
			st = new AssumeStatement(loc, falseLiteral);
		}
		return new ExpressionResult(Collections.singletonList(st), null);
	}

	private static Result handleLtlStep(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final LTLStepAnnotation ltlStep = new LTLStepAnnotation();
		final AssumeStatement assumeStmt =
				new AssumeStatement(loc, new BooleanLiteral(loc, new InferredType(Type.Boolean), true));
		ltlStep.annotate(assumeStmt);
		return new ExpressionResult(Collections.singletonList(assumeStmt), null);
	}

	private static Result handleByIgnore(final Dispatcher main, final ILocation loc, final String methodName) {
		main.warn(loc, "ignored call to " + methodName);
		return new SkipResult();
	}

	private static Result handleByUnsupportedSyntaxException(final ILocation loc, final String functionName) {
		throw new UnsupportedSyntaxException(loc, "Unsupported function: " + functionName);
	}

	private static ExpressionResult combineExpressionResults(final LRValue finalLRValue,
			final List<ExpressionResult> results) {
		final List<Statement> stmt = new ArrayList<>();
		final List<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final List<Overapprox> overapprox = new ArrayList<>();

		for (final ExpressionResult result : results) {
			stmt.addAll(result.getStatements());
			decl.addAll(result.getDeclarations());
			auxVars.putAll(result.getAuxVars());
			overapprox.addAll(result.getOverapprs());
		}

		return new ExpressionResult(stmt, finalLRValue, decl, auxVars, overapprox);
	}

	private static ExpressionResult combineExpressionResults(final LRValue finalLRValue,
			final ExpressionResult... results) {
		return combineExpressionResults(finalLRValue, Arrays.stream(results).collect(Collectors.toList()));
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	@FunctionalInterface
	private interface IFunctionModelHandler {
		Result handleFunction(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
				String methodName);
	}

}
