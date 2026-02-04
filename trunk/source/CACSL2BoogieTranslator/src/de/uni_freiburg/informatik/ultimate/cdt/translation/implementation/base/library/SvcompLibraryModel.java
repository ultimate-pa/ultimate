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
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;

/**
 * Model of SV-COMP specific functions, see https://sv-comp.sosy-lab.org/2025/rules.php under Benchmark Verification
 * Tasks. This includes functions to receive non-deterministic values (__VERIFIER_nondet_X) and functions for atomic
 * blocks (__VERIFIER_atomic_*). Note: These functions do not occur in the C standard or any of the libraries!
 */
public class SvcompLibraryModel implements ILibraryModel {
	/**
	 * If we construct an auxvar that models a nondeterministic input, we havoc that auxvar afterwards to ensure that we
	 * get a new nondeterministic value even if the variable occurs in a loop. If this constant is set, we havoc the
	 * variable also before the nondeterministic assignment. If the auxvar is also havoced before, it is only
	 * backward-live to the havoc, otherwise it would be backward-live until the beginning of the procedure.
	 */
	private static final boolean HAVOC_NONDET_AUXVARS_ALSO_BEFORE = true;

	private final FunctionModelHelper mHelper;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final ExpressionTranslation mExpressionTranslation;
	private final INameHandler mNameHandler;
	private final boolean mCheckErrorFunction;
	private final ExpressionResultTransformer mExprResultTransformer;

	public SvcompLibraryModel(final FunctionModelHelper helper, final AuxVarInfoBuilder auxVarInfoBuilder,
			final ExpressionTranslation expressionTranslation, final INameHandler nameHandler,
			final boolean checkErrorFunction, final ExpressionResultTransformer exprResultTransformer) {
		mHelper = helper;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mExpressionTranslation = expressionTranslation;
		mNameHandler = nameHandler;
		mCheckErrorFunction = checkErrorFunction;
		mExprResultTransformer = exprResultTransformer;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		result.add(new FunctionModel("__VERIFIER_ltl_step", (main, node, loc, name) -> handleLtlStep(main, node, loc)));
		result.add(new FunctionModel("__VERIFIER_error", this::handleErrorFunction));
		result.add(new FunctionModel("reach_error", this::handleErrorFunction));

		result.add(new FunctionModel("__VERIFIER_assume", this::handleVerifierAssume));

		result.add(new FunctionModel("__VERIFIER_nondet_bool",
				(main, node, loc, name) -> handleVerifierNondetBool(main, loc)));
		result.add(new FunctionModel("__VERIFIER_nondet__Bool",
				(main, node, loc, name) -> handleVerifierNondetBool(main, loc)));
		result.add(new FunctionModel("__VERIFIER_nondet_char",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.CHAR))));
		result.add(new FunctionModel("__VERIFIER_nondet_pchar", (main, node, loc, name) -> handleVerifierNonDet(main,
				loc, new CPointer(new CPrimitive(CPrimitives.CHAR)))));
		result.add(new FunctionModel("__VERIFIER_nondet_charp", (main, node, loc, name) -> handleVerifierNonDet(main,
				loc, new CPointer(new CPrimitive(CPrimitives.CHAR)))));
		result.add(new FunctionModel("__VERIFIER_nondet_float",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("__VERIFIER_nondet_double",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("__VERIFIER_nondet_int",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("__VERIFIER_nondet_long",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("__VERIFIER_nondet_longlong",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONGLONG))));
		result.add(new FunctionModel("__VERIFIER_nondet_int128",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT128))));
		result.add(new FunctionModel("__VERIFIER_nondet_short",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.SHORT))));
		result.add(new FunctionModel("__VERIFIER_nondet_uchar",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UCHAR))));
		result.add(new FunctionModel("__VERIFIER_nondet_unsigned_char",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UCHAR))));
		result.add(new FunctionModel("__VERIFIER_nondet_unsigned",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT))));
		result.add(new FunctionModel("__VERIFIER_nondet_unsigned_int",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT))));
		result.add(new FunctionModel("__VERIFIER_nondet_uint",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT))));
		result.add(new FunctionModel("__VERIFIER_nondet_ulong",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("__VERIFIER_nondet_ulonglong",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONGLONG))));
		result.add(new FunctionModel("__VERIFIER_nondet_uint128",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT128))));
		result.add(new FunctionModel("__VERIFIER_nondet_ushort",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.USHORT))));

		// TODO: These are no predefined types, thus the return value may depend on the benchmark
		result.add(new FunctionModel("__VERIFIER_nondet_loff_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("__VERIFIER_nondet_size_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("__VERIFIER_nondet_pthread_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("__VERIFIER_nondet_sector_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("__VERIFIER_nondet_u8",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UCHAR))));
		result.add(new FunctionModel("__VERIFIER_nondet_u16",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.USHORT))));
		result.add(new FunctionModel("__VERIFIER_nondet_u32",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT))));

		result.add(new FunctionModel("__VERIFIER_atomic_begin", (main, node, loc, name) -> handleByFunctionCall(main,
				node, loc, name, new CPrimitive(CPrimitives.VOID))));
		result.add(new FunctionModel("__VERIFIER_atomic_end", (main, node, loc, name) -> handleByFunctionCall(main,
				node, loc, name, new CPrimitive(CPrimitives.VOID))));

		return result;
	}

	private ExpressionResult handleVerifierNondetBool(final IDispatcher main, final ILocation loc) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final CPrimitive cType = new CPrimitive(CPrimitives.BOOL);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		resultBuilder.addAuxVarWithDeclaration(auxvarinfo);
		if (HAVOC_NONDET_AUXVARS_ALSO_BEFORE) {
			resultBuilder.addStatement(new HavocStatement(loc, new VariableLHS[] { auxvarinfo.getLhs() }));
		}
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), cType));
		final Expression isZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, auxvarinfo.getExp(),
				mExpressionTranslation.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO));
		final Expression isOne = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, auxvarinfo.getExp(),
				mExpressionTranslation.constructLiteralForIntegerType(loc, cType, BigInteger.ONE));
		resultBuilder.addStatement(new AssumeStatement(loc, ExpressionFactory.or(loc, List.of(isZero, isOne))));

		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		return resultBuilder.build();
	}

	private ExpressionResult handleVerifierNonDet(final IDispatcher main, final ILocation loc, final ICType cType) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		resultBuilder.addAuxVarWithDeclaration(auxvarinfo);
		if (HAVOC_NONDET_AUXVARS_ALSO_BEFORE) {
			resultBuilder.addStatement(new HavocStatement(loc, new VariableLHS[] { auxvarinfo.getLhs() }));
		}
		final LRValue returnValue = new RValue(auxvarinfo.getExp(), cType);
		resultBuilder.setLrValue(returnValue);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(),
				resultBuilder);

		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		return resultBuilder.build();
	}

	private Result handleErrorFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final Expression falseLiteral = ExpressionFactory.createBooleanLiteral(loc, false);
		final Statement st = mHelper.createAnnotatedAssertOrAssume(loc, name, mCheckErrorFunction, Spec.ERROR_FUNCTION,
				falseLiteral);
		return new ExpressionResult(Collections.singletonList(st), null);
	}

	private ExpressionResult handleByFunctionCall(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final ICType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final IASTInitializerClause[] arguments = node.getArguments();
		final Expression[] translatedArgs = new Expression[arguments.length];
		for (int i = 0; i < arguments.length; i++) {
			final ExpressionResult dispatched = (ExpressionResult) main.dispatch(arguments[i]);
			builder.addAllExceptLrValue(dispatched);
			translatedArgs[i] = dispatched.getLrValue().getValue();
		}
		VariableLHS[] retValue;
		if (resultType.isVoidType()) {
			retValue = new VariableLHS[0];
		} else {
			final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, AUXVAR.RETURNED);
			builder.addAuxVarWithDeclaration(auxVar);
			retValue = new VariableLHS[] { auxVar.getLhs() };
		}
		builder.addStatement(StatementFactory.constructCallStatement(loc, false, retValue, name, translatedArgs));
		return builder.build();
	}

	private Result handleVerifierAssume(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		// according to SV-Comp specification assume takes only one argument, but the code allows more than one
		mHelper.checkArguments(loc, 1, name, node.getArguments());

		final List<Expression> args = new ArrayList<>();
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause inParam : node.getArguments()) {
			ExpressionResult in = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, inParam);
			if (in.getLrValue().getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}
			in = mExprResultTransformer.rexIntToBool(in, loc);
			args.add(in.getLrValue().getValue());
			results.add(in);
		}

		final ExpressionResultBuilder rtr = new ExpressionResultBuilder().addAllExceptLrValue(results);
		for (final Expression a : args) {
			// could just take the first as there is only one, but it's so easy to make it more general..
			rtr.addStatement(new AssumeStatement(loc, a));
		}
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr.build();
	}

	private static Result handleLtlStep(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final NamedAttribute ltlAttribute = new NamedAttribute(loc, "ltl_step", new Expression[] {});
		final AssumeStatement assumeStmt = new AssumeStatement(loc, new NamedAttribute[] { ltlAttribute },
				ExpressionFactory.createBooleanLiteral(loc, true));
		return new ExpressionResult(Collections.singletonList(assumeStmt), null);
	}
}
