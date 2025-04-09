package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;

public class SvcompFunctionHandler extends StandardFunctionHandler2 {
	/**
	 * If we construct an auxvar that models a nondeterministic input, we havoc that auxvar afterwards to ensure that we
	 * get a new nondeterministic value even if the variable occurs in a loop. If this constant is set, we havoc the
	 * variable also before the nondeterministic assignment. If the auxvar is also havoced before, it is only
	 * backward-live to the havoc, otherwise it would be backward-live until the beginning of the procedure.
	 */
	private static final boolean HAVOC_NONDET_AUXVARS_ALSO_BEFORE = true;

	public SvcompFunctionHandler(final Map<String, IASTNode> functionTable, final AuxVarInfoBuilder auxVarInfoBuilder,
			final INameHandler nameHandler, final ExpressionTranslation expressionTranslation,
			final MemoryHandler memoryHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final ProcedureManager procedureManager, final TypeSizes typeSizes, final TranslationSettings settings,
			final ExpressionResultTransformer expressionResultTransformer, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		super(functionTable, auxVarInfoBuilder, nameHandler, expressionTranslation, memoryHandler,
				typeSizeAndOffsetComputer, procedureManager, typeSizes, settings, expressionResultTransformer,
				typeHandler, cEpressionTranslator, dataRaceChecker);
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

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
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
		final Statement st = createAnnotatedAssertOrAssume(loc, name, mSettings.checkErrorFunction(),
				Spec.ERROR_FUNCTION, falseLiteral);
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
		checkArguments(loc, 1, name, node.getArguments());

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
