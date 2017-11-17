/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
/**
 * CHandler variation for the SV-COMP 2014.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svcomp;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTName;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LTLStepAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;

/**
 * @author Markus Lindenmann, Matthias Heizmann
 * @date 12.6.2012
 */
public class SvComp14CHandler extends CHandler {

	private static final int ARGS_COUNT_BUILTIN_MEMCPY = 3;

	private final Map<String, IFunctionModelHandler> mFunctionModels;

	/**
	 * Constructor.
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param bitvectorTranslation
	 * @param overapproximateFloatingPointOperations
	 */
	public SvComp14CHandler(final Dispatcher main, final CACSL2BoogieBacktranslator backtranslator,
			final ILogger logger, final ITypeHandler typeHandler, final boolean bitvectorTranslation,
			final boolean overapproximateFloatingPointOperations, final INameHandler nameHandler) {
		super(main, backtranslator, false, logger, typeHandler, bitvectorTranslation,
				overapproximateFloatingPointOperations, nameHandler);
		mFunctionModels = getFunctionModels();
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

		// TODO: __builtin_isgreater, __builtin_isgreaterequal, __builtin_isunordered, __builtin_islessgreater,
		// __builtin_islessequal, __builtin_isless

		map.put("abort", (main, node, loc, name) -> handleAbort(loc));

		map.put("printf", (main, node, loc, name) -> handlePrintF(main, node, loc));

		map.put("__builtin_memcpy", (main, node, loc, name) -> handleMemCopy(main, node, loc));
		map.put("memcpy", (main, node, loc, name) -> handleMemCopy(main, node, loc));

		map.put("nan", (main, node, loc, name) -> handleNaN(loc, name));
		map.put("nanf", (main, node, loc, name) -> handleNaN(loc, name));
		map.put("nanl", (main, node, loc, name) -> handleNaN(loc, name));
		map.put("__builtin_nan", (main, node, loc, name) -> handleNaN(loc, "nan"));
		map.put("__builtin_nanf", (main, node, loc, name) -> handleNaN(loc, "nanf"));
		map.put("__builtin_nanl", (main, node, loc, name) -> handleNaN(loc, "nanl"));
		map.put("__builtin_inff", (main, node, loc, name) -> handleNaN(loc, "inff"));

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
		map.put("__VERIFIER_nondet_pointer",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.VOID)));
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

	private Result handleBuiltinExpect(final Dispatcher main, final IASTFunctionCallExpression node) {
		// this is a gcc-builtin function that helps with branch prediction, it always returns the first argument.
		return main.dispatch(node.getArguments()[0]);
	}

	private static ExpressionResult handleAbort(final ILocation loc) {
		return new ExpressionResult(Collections.singletonList(new AssumeStatement(loc, new BooleanLiteral(loc, false))),
				null);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTFunctionCallExpression node) {

		if (!(node.getFunctionNameExpression() instanceof IASTIdExpression)) {
			return super.visit(main, node);
		}

		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final IASTIdExpression astIdExpression = (IASTIdExpression) node.getFunctionNameExpression();
		final String methodName = astIdExpression.getName().toString();

		final IFunctionModelHandler functionModel = mFunctionModels.get(methodName);
		if (functionModel != null) {
			return functionModel.handleFunction(main, node, loc, methodName);
		}

		return super.visit(main, node);
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

		assert isAuxVarMapcomplete(main.mNameHandler, decl, auxVars);
		return new ExpressionResult(stmt, returnValue, decl, auxVars);
	}

	private Result handleVerifierAssume(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final List<Statement> stmt = new ArrayList<>();
		final List<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final List<Overapprox> overappr = new ArrayList<>();
		final LRValue returnValue = null;
		final ArrayList<Expression> args = new ArrayList<>();
		for (final IASTInitializerClause inParam : node.getArguments()) {
			final ExpressionResult in = ((ExpressionResult) main.dispatch(inParam)).switchToRValueIfNecessary(main,
					getMemoryHandler(), mStructHandler, loc);
			if (in.lrVal.getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}
			in.rexIntToBoolIfNecessary(loc, mExpressionTranslation, getMemoryHandler());
			args.add(in.lrVal.getValue());
			stmt.addAll(in.stmt);
			decl.addAll(in.decl);
			auxVars.putAll(in.auxVars);
			overappr.addAll(in.overappr);
		}
		// according to SV-Comp specification!
		assert args.size() == 1;
		for (final Expression a : args) {
			// could just take the first as there is only one, but it's so easy to make it more general..
			stmt.add(new AssumeStatement(loc, a));
		}
		assert isAuxVarMapcomplete(main.mNameHandler, decl, auxVars);
		return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
	}

	private Result handleNaN(final ILocation loc, final String methodName) {
		return mExpressionTranslation.createNanOrInfinity(loc, methodName);
	}

	private Result handleBuiltinObjectSize(final Dispatcher main, final ILocation loc) {
		main.warn(loc, "used trivial implementation of __builtin_object_size");
		final CPrimitive cType = new CPrimitive(CPrimitives.INT);
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO);
		return new ExpressionResult(new RValue(zero, cType));
	}

	private Result handlePrintF(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		final List<Statement> stmt = new ArrayList<>();
		final List<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final List<Overapprox> overappr = new ArrayList<>();
		LRValue returnValue;
		// skip if parent of parent is CompoundStatement
		// otherwise, replace by havoced variable
		if (node.getParent().getParent() instanceof IASTCompoundStatement) {
			return new SkipResult();
		}
		// 2015-11-05 Matthias: TODO check if int is reasonable here
		final CType returnType = new CPrimitive(CPrimitives.INT);
		final ASTType tempType = mTypeHandler.cType2AstType(loc, returnType);
		final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, null);
		final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { tId }, tempType) });
		auxVars.put(tVarDecl, loc);
		decl.add(tVarDecl);
		stmt.add(new HavocStatement(loc, new VariableLHS[] { new VariableLHS(loc, tId) }));
		returnValue = new RValue(new IdentifierExpression(loc, tId), null);
		assert isAuxVarMapcomplete(main.mNameHandler, decl, auxVars);
		return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
	}

	private Result handleMemCopy(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		assert node.getArguments().length == ARGS_COUNT_BUILTIN_MEMCPY : "wrong number of arguments";
		ExpressionResult dest = (ExpressionResult) handleBuiltinExpect(main, node);
		dest = dest.switchToRValueIfNecessary(main, getMemoryHandler(), mStructHandler, loc);
		main.mCHandler.convert(loc, dest, new CPointer(new CPrimitive(CPrimitives.VOID)));
		ExpressionResult src = (ExpressionResult) main.dispatch(node.getArguments()[1]);
		src = src.switchToRValueIfNecessary(main, getMemoryHandler(), mStructHandler, loc);
		main.mCHandler.convert(loc, src, new CPointer(new CPrimitive(CPrimitives.VOID)));
		ExpressionResult size = (ExpressionResult) main.dispatch(node.getArguments()[2]);
		size = size.switchToRValueIfNecessary(main, getMemoryHandler(), mStructHandler, loc);
		main.mCHandler.convert(loc, size, mTypeSizeComputer.getSizeT());

		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(dest, src, size);

		final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MEMCPYRES, dest.lrVal.getCType());
		final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { tId }, main.mTypeHandler.constructPointerType(loc)) });
		result.decl.add(tVarDecl);
		result.auxVars.put(tVarDecl, loc);

		final Statement call = getMemoryHandler().constructMemcpyCall(loc, dest.lrVal.getValue(), src.lrVal.getValue(),
				size.lrVal.getValue(), tId);
		result.stmt.add(call);
		result.lrVal = new RValue(new IdentifierExpression(loc, tId), new CPointer(new CPrimitive(CPrimitives.VOID)));

		// add required information to function handler.
		getFunctionHandler().addCallGraphNode(MemoryModelDeclarations.C_Memcpy.getName());
		getFunctionHandler().addCallGraphEdge(getFunctionHandler().getCurrentProcedureID(),
				MemoryModelDeclarations.C_Memcpy.getName());
		getFunctionHandler().addModifiedGlobalEntry(MemoryModelDeclarations.C_Memcpy.getName());

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

	@Override
	public Result visit(final Dispatcher main, final IASTIdExpression node) {
		if (node == null) {
			throw new IllegalArgumentException("node");
		}
		final IASTName nodeName = node.getName();
		if (nodeName == null) {
			throw new IllegalArgumentException("node has no name");
		}
		final String nodeNameStr = nodeName.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);

		if ("null".equals(nodeNameStr)) {
			return new ExpressionResult(new RValue(mExpressionTranslation.constructNullPointer(loc),
					new CPointer(new CPrimitive(CPrimitives.VOID))));
		}
		if ("__PRETTY_FUNCTION__".equals(nodeNameStr) || "__FUNCTION__".equals(nodeNameStr)) {
			final CType returnType = new CPointer(new CPrimitive(CPrimitives.CHAR));
			final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, returnType);
			final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] {
					new VarList(loc, new String[] { tId }, main.mTypeHandler.constructPointerType(loc)) });
			final RValue rvalue = new RValue(new IdentifierExpression(loc, tId), returnType);
			final ArrayList<Declaration> decls = new ArrayList<>();
			decls.add(tVarDecl);
			final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
			auxVars.put(tVarDecl, loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, auxVars);
		}
		return super.visit(main, node);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTASMDeclaration node) {
		// workaround for now: ignore inline assembler instructions
		return new SkipResult();
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
