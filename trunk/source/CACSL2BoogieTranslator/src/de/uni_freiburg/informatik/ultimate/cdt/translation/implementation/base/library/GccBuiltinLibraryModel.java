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
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryArea;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Model for various GCC builtin functions (see https://gcc.gnu.org/onlinedocs/gcc/Built-in-Functions.html)
 */
public class GccBuiltinLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final MemoryHandler mMemoryHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeComputer;

	public GccBuiltinLibraryModel(final FunctionModelHelper helper,
			final ExpressionResultTransformer exprResultTransformer, final ExpressionTranslation expressionTranslation,
			final AuxVarInfoBuilder auxVarInfoBuilder, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeComputer) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mMemoryHandler = memoryHandler;
		mTypeSizeComputer = typeSizeComputer;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		result.add(new FunctionModel("alloca", this::handleAlloc));
		result.add(new FunctionModel("__builtin_alloca", this::handleAlloc));

		/*
		 * The GNU C online documentation at https://gcc.gnu.org/onlinedocs/gcc/Return-Address.html on 09 Nov 2016 says:
		 * "— Built-in Function: void * __builtin_return_address (unsigned int level) This function returns the return
		 * address of the current function, or of one of its callers. The level argument is number of frames to scan up
		 * the call stack. A value of 0 yields the return address of the current function, a value of 1 yields the
		 * return address of the caller of the current function, and so forth. When inlining the expected behavior is
		 * that the function returns the address of the function that is returned to. To work around this behavior use
		 * the noinline function attribute.
		 *
		 * The level argument must be a constant integer. On some machines it may be impossible to determine the return
		 * address of any function other than the current one; in such cases, or when the top of the stack has been
		 * reached, this function returns 0 or a random value. In addition, __builtin_frame_address may be used to
		 * determine if the top of the stack has been reached. Additional post-processing of the returned value may be
		 * needed, see __builtin_extract_return_addr. Calling this function with a nonzero argument can have
		 * unpredictable effects, including crashing the calling program. As a result, calls that are considered unsafe
		 * are diagnosed when the -Wframe-address option is in effect. Such calls should only be made in debugging
		 * situations."
		 *
		 * Current solution: replace call by a havoced aux variable.
		 */
		result.add(new FunctionModel("__builtin_return_address", (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 1, CPointer.voidPointer())));

		result.add(new FunctionModel("__builtin_bswap16", (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 1, new CPrimitive(CPrimitives.USHORT))));
		result.add(new FunctionModel("__builtin_bswap32", (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 1, new CPrimitive(CPrimitives.UINT))));
		result.add(new FunctionModel("__builtin_bswap64", (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 1, new CPrimitive(CPrimitives.ULONG))));

		result.add(new FunctionModel("__builtin_constant_p", (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 1, new CPrimitive(CPrimitives.BOOL))));
		result.add(new FunctionModel("__builtin_isinf_sign", (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 1, new CPrimitive(CPrimitives.INT))));

		/*
		 * 6.56 Built-in Functions to Perform Arithmetic with Overflow Checking
		 * https://gcc.gnu.org/onlinedocs/gcc/Integer-Overflow-Builtins.html
		 */
		final IFunctionModelHandler overapproximateGccOverflowCheck = (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 3, new CPrimitive(CPrimitives.BOOL));
		result.add(new FunctionModel("__builtin_sadd_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_plus, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("__builtin_saddl_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_plus, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("__builtin_saddll_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_plus, new CPrimitive(CPrimitives.LONGLONG))));
		result.add(new FunctionModel("__builtin_uadd_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_plus, new CPrimitive(CPrimitives.UINT))));
		result.add(new FunctionModel("__builtin_uaddl_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_plus, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("__builtin_uaddll_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_plus, new CPrimitive(CPrimitives.ULONGLONG))));
		result.add(new FunctionModel("__builtin_ssub_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_minus, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("__builtin_ssubl_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_minus, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("__builtin_ssubll_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_minus, new CPrimitive(CPrimitives.LONGLONG))));
		result.add(new FunctionModel("__builtin_usub_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_minus, new CPrimitive(CPrimitives.UINT))));
		result.add(new FunctionModel("__builtin_usubl_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_minus, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("__builtin_usubll_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_minus, new CPrimitive(CPrimitives.ULONGLONG))));
		result.add(new FunctionModel("__builtin_smul_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_multiply, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("__builtin_smull_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_multiply, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("__builtin_smulll_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_multiply, new CPrimitive(CPrimitives.LONGLONG))));
		result.add(new FunctionModel("__builtin_umul_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_multiply, new CPrimitive(CPrimitives.UINT))));
		result.add(new FunctionModel("__builtin_umull_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_multiply, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("__builtin_umulll_overflow", (main, node, loc, name) -> handleBuiltinOverflow(main,
				node, loc, name, IASTBinaryExpression.op_multiply, new CPrimitive(CPrimitives.ULONGLONG))));
		result.add(new FunctionModel("__builtin_add_overflow_p", overapproximateGccOverflowCheck));
		result.add(new FunctionModel("__builtin_sub_overflow_p", overapproximateGccOverflowCheck));
		result.add(new FunctionModel("__builtin_mul_overflow_p", overapproximateGccOverflowCheck));

		/*
		 * builtin_prefetch according to https://gcc.gnu.org/onlinedocs/gcc-3.4.5/gcc/Other-Builtins.html (state:
		 * 5.6.2015) triggers the processor to load something into cache, does nothing else is void thus has no return
		 * value
		 */
		result.add(new FunctionModel("__builtin_prefetch", (main, node, loc, name) -> new SkipResult()));

		result.add(new FunctionModel("__builtin_expect", this::handleBuiltinExpect));
		result.add(
				new FunctionModel("__builtin_unreachable", (main, node, loc, name) -> handleBuiltinUnreachable(loc)));
		result.add(new FunctionModel("__builtin_object_size", this::handleBuiltinObjectSize));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		/*
		 * See https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
		 */
		return List.of("__builtin_popcount", "__builtin_popcountl", "__builtin_popcountll", "__builtin_add_overflow",
				"__builtin_mul_overflow", "__builtin_sub_overflow");
	}

	private static Result handleBuiltinUnreachable(final ILocation loc) {
		/*
		 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
		 *
		 * Built-in Function: void __builtin_unreachable (void)
		 *
		 * If control flow reaches the point of the __builtin_unreachable, the program is undefined. It is useful in
		 * situations where the compiler cannot deduce the unreachability of the code.
		 */

		// TODO: Add option that allows us to check for builtin_unreachable by adding assert
		// return new ExpressionResult(Collections.singletonList(new AssertStatement(loc,
		// new de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral(loc, false))), null);
		// TODO: Add option that just ignores the function:
		// return new SkipResult();
		// TODO: Keep the following code, but add it as option together with the other two
		return new ExpressionResult(
				List.of(new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false))), null);
	}

	private Result handleBuiltinExpect(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		/**
		 * Built-in Function: long __builtin_expect (long exp, long c)
		 *
		 * You may use __builtin_expect to provide the compiler with branch prediction information. In general, you
		 * should prefer to use actual profile feedback for this (-fprofile-arcs), as programmers are notoriously bad at
		 * predicting how their programs actually perform. However, there are applications in which this data is hard to
		 * collect.
		 *
		 * The return value is the value of exp, which should be an integral expression. The semantics of the built-in
		 * are that it is expected that exp == c. For example:
		 *
		 * <code>if (__builtin_expect (x, 0)) foo ();</code>
		 *
		 * indicates that we do not expect to call foo, since we expect x to be zero. Since you are limited to integral
		 * expressions for exp, you should use constructions such as
		 *
		 * <code>if (__builtin_expect (ptr != NULL, 1)) foo (*ptr);</code>
		 *
		 * when testing pointer or floating-point values.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);
		final ExpressionResult arg1 =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult arg2 =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		return new ExpressionResultBuilder().addAllExceptLrValue(arg1, arg2).setLrValue(arg1.getLrValue()).build();
	}

	/**
	 * See https://gcc.gnu.org/onlinedocs/gcc/Integer-Overflow-Builtins.html for specification
	 */
	private Result handleBuiltinOverflow(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final int operator, final CPrimitive resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult left = mExprResultTransformer.convertIfNecessary(loc,
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]), resultType);
		final ExpressionResult right = mExprResultTransformer.convertIfNecessary(loc,
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]), resultType);
		builder.addAllExceptLrValue(left, right);
		// Apply the operator to the first two parameters with infinite precision (i.e. ignoring any wraparound or
		// overflows), convert the result to the given type and write it to the third argument.
		final Pair<Expression, ASTType> infinitePrecisionResult =
				mExpressionTranslation.constructInfinitePrecisionOperation(loc, operator, left.getLrValue().getValue(),
						right.getLrValue().getValue(), resultType);
		final Expression infinitePrecisionExpr = infinitePrecisionResult.getFirst();
		final ASTType infinitePrecisionType = infinitePrecisionResult.getSecond();
		// Write the (converted) result of the operation to the third argument
		final ExpressionResult resPointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[2]);
		builder.addAllExceptLrValue(resPointer);
		builder.addAllExceptLrValue(mExprResultTransformer.makePointerAssignment(loc, resPointer.getLrValue(),
				mExpressionTranslation.convertInfinitePrecisionExpression(loc, infinitePrecisionExpr, resultType)));
		// If the infinite precision result fits in the given type, return 0 otherwise 1.
		final Expression inRange = mExpressionTranslation.checkInRangeInfinitePrecision(loc, infinitePrecisionExpr,
				infinitePrecisionType, resultType);
		final CPrimitive boolType = new CPrimitive(CPrimitives.BOOL);
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc, boolType, BigInteger.ZERO);
		final Expression one = mExpressionTranslation.constructLiteralForIntegerType(loc, boolType, BigInteger.ONE);
		final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, inRange, zero, one);
		return builder.setLrValue(new RValue(resultExpr, boolType)).build();
	}

	private Result handleBuiltinObjectSize(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		// DD: builtin-object size is way more complicated that the old implementation!
		// Read https://gcc.gnu.org/onlinedocs/gcc/Object-Size-Checking.html
		// For testing, overapproximate and do not dispatch arguments (I understand the spec as this is whats happening,
		// but I am not sure)
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);
		return mHelper.constructOverapproximationForFunctionCall(loc, name, new CPrimitive(CPrimitives.INT));
	}

	private Result handleAlloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, methodName, arguments);

		final ExpressionResult exprRes =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult exprResConverted =
				mExprResultTransformer.performImplicitConversion(exprRes, mTypeSizeComputer.getSizeT(), loc);
		final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(exprResConverted);
		final CPointer resultType = CPointer.voidPointer();
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MALLOC);
		erb.addAuxVarWithDeclaration(auxvar);

		erb.addStatement(mMemoryHandler.getUltimateMemAllocCall(exprResConverted.getLrValue().getValue(),
				auxvar.getLhs(), loc, MemoryArea.STACK));
		erb.setLrValue(new RValue(auxvar.getExp(), resultType));

		// for alloc a we have to free the variable ourselves when the
		// stackframe is closed, i.e. at a return
		final LocalLValue llVal = new LocalLValue(auxvar.getLhs(), resultType, null);
		mMemoryHandler
				.addVariableToBeFreed(new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
		// we need to clear auxVars because otherwise the malloc auxvar is havocced after
		// this, and free (triggered by the statement before) would fail.
		erb.clearAuxVars();
		return erb.build();
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		// DD 2020-12-02: Not entirely accurate, because it is actually architecture dependent.
		// see https://en.wikipedia.org/wiki/Quadruple-precision_floating-point_format and
		// https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
		return List.of(new TypeModel("__float128", new CPrimitive(CPrimitives.LONGDOUBLE)));
	}

	private ExpressionResult handleFunction(final ILocation loc) {
		final ICType returnType = new CPointer(new CPrimitive(CPrimitives.CHAR));
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnType, SFO.AUXVAR.NONDET);
		final RValue rvalue = new RValue(auxvar.getExp(), returnType);
		return new ExpressionResult(List.of(), rvalue, List.of(auxvar.getVarDec()), Set.of(auxvar));
	}

	private ConstantModel modelSizeofConstant(final String name, final ICType type) {
		return new ConstantModel(name, loc -> new ExpressionResult(
				new RValue(mTypeSizeComputer.constructBytesizeExpression(loc, type), type)));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		return List.of(new ConstantModel("__PRETTY_FUNCTION__", this::handleFunction),
				new ConstantModel("__FUNCTION__", this::handleFunction),
				new ConstantModel("__func__", this::handleFunction),
				modelSizeofConstant("__SIZEOF_INT__", new CPrimitive(CPrimitives.INT)),
				modelSizeofConstant("__SIZEOF_LONG__", new CPrimitive(CPrimitives.LONG)),
				modelSizeofConstant("__SIZEOF_LONG_LONG__", new CPrimitive(CPrimitives.LONGLONG)),
				modelSizeofConstant("__SIZEOF_SHORT__", new CPrimitive(CPrimitives.SHORT)),
				modelSizeofConstant("__SIZEOF_POINTER__", CPointer.voidPointer()),
				modelSizeofConstant("__SIZEOF_FLOAT__", new CPrimitive(CPrimitives.FLOAT)),
				modelSizeofConstant("__SIZEOF_DOUBLE__", new CPrimitive(CPrimitives.DOUBLE)),
				modelSizeofConstant("__SIZEOF_LONG_DOUBLE__", new CPrimitive(CPrimitives.LONGDOUBLE)),
				modelSizeofConstant("__SIZEOF_SIZE_T__", mTypeSizeComputer.getSizeT()),
				modelSizeofConstant("__SIZEOF_INT128__", new CPrimitive(CPrimitives.INT128)));
	}
}
