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
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
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
	
	/**
	 * The string representing SV-Comp's error method.
	 */
	private static final String ERROR_STRING = "__VERIFIER_error";
	/**
	 * The string representing SV-Comp's havoc method.
	 */
	private static final String NONDET_STRING = "__VERIFIER_nondet_";
	/**
	 * Nondet_X | X in {int, float, char, short, long, pointer}
	 */
	private static final String[] NONDET_TYPE_STRINGS = { 
			"_Bool","bool","char","float","double","size_t","int","loff_t",
			"long","short","pchar","pointer","uchar","unsigned","uint","ulong","ushort" };
	/**
	 * The string representing SV-Comp's assert method.
	 */
	private static final String ASSUME_STRING = "__VERIFIER_assume";
	
	private static final String[] s_UNSUPPORTED_FLOAT_OPERATIONS = {
		"sin"
	};
	private final HashSet<String> mUnsupportedFloatOperations = 
			new HashSet<>(Arrays.asList(s_UNSUPPORTED_FLOAT_OPERATIONS));

	/**
	 * Constructor.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param bitvectorTranslation 
	 * @param overapproximateFloatingPointOperations 
	 */
	public SvComp14CHandler(Dispatcher main, CACSL2BoogieBacktranslator backtranslator, 
			ILogger logger, ITypeHandler typeHandler, boolean bitvectorTranslation, boolean overapproximateFloatingPointOperations, INameHandler nameHandler) {
		super(main, backtranslator, false, logger, typeHandler, bitvectorTranslation, overapproximateFloatingPointOperations, nameHandler);
	}

	//
	// __VERIFIER_assume(EXPR) && skip VERIFIER_nondet_X()
	//

	@Override
	public Result visit(Dispatcher main, IASTFunctionCallExpression node) {
		final ILocation loc = LocationFactory.createCLocation(node);

		if (!(node.getFunctionNameExpression() instanceof IASTIdExpression)) {
			return super.visit(main, node);
		}
		final IASTIdExpression astIdExpression = (IASTIdExpression) node.getFunctionNameExpression();
		final String methodName = astIdExpression.getName().toString();

		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
		LRValue returnValue = null;
		
		if (methodName.equals("pthread_create")) {
			throw new UnsupportedSyntaxException(loc, "we do not support pthread");
		}
		if (mUnsupportedFloatOperations.contains(methodName)) {
			throw new UnsupportedSyntaxException(loc, "unsupported float operation " + methodName);
		}
		if (methodName.equals(ERROR_STRING)) {
			final boolean checkSvcompErrorfunction = 
					main.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SVCOMP_ERRORFUNCTION);
			if (checkSvcompErrorfunction) {
				final Check check = new Check(Spec.ERROR_Function);
				final AssertStatement assertStmt = new AssertStatement(loc, new BooleanLiteral(loc,
						new InferredType(Type.Boolean), false));
				check.addToNodeAnnot(assertStmt);
				stmt.add(assertStmt);
			} 
			return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
		}
		if (methodName.equals(ASSUME_STRING)) {
			final ArrayList<Expression> args = new ArrayList<Expression>();
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
			assert args.size() == 1; // according to SV-Comp specification!
			for (final Expression a : args) {
//			could just take the first as there is only one, but it's so easy to make it more general..
				stmt.add(new AssumeStatement(loc, a));
			}
			assert (isAuxVarMapcomplete(main.mNameHandler, decl, auxVars));
			return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
		}
		for (final String t : NONDET_TYPE_STRINGS) {
			if (methodName.equals(NONDET_STRING + t)) {
				
				CType cType;
				switch (t) {
				case "_Bool":
				case "bool":
					cType = new CPrimitive(CPrimitives.BOOL);
					break;
				case "char":
					cType = new CPrimitive(CPrimitives.CHAR);
					break;
				case "float":
					cType = new CPrimitive(CPrimitives.FLOAT);
//					throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), "we do not support floats");
					break;
				case "double":
					cType = new CPrimitive(CPrimitives.DOUBLE);
//					throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), "we do not support floats");
					break;
				case "size_t":
				case "int":
					cType = new CPrimitive(CPrimitives.INT);
					break;
				case "loff_t":
				case "long":
					cType = new CPrimitive(CPrimitives.LONG);
					break;
				case "short":
					cType = new CPrimitive(CPrimitives.SHORT);
					break;
				case "pchar":
					cType = new CPointer(new CPrimitive(CPrimitives.CHAR));
					break;
				case "pointer":
//					NamedType boogiePointerType = new NamedType(null, new InferredType(Type.Struct), SFO.POINTER,
//							new ASTType[0]);
//					type = boogiePointerType;
					cType = new CPointer(new CPrimitive(CPrimitives.VOID));
					break;
				case "uchar":
					cType = new CPrimitive(CPrimitives.UCHAR);
					break;
				case "unsigned":
				case "uint":
					cType = new CPrimitive(CPrimitives.UINT);
					break;
				case "ulong":
					cType = new CPrimitive(CPrimitives.ULONG);
					break;
				case "ushort":
					cType = new CPrimitive(CPrimitives.USHORT);
					break;
				default:
					throw new AssertionError("unknown type " + t);
				}
				final ASTType type = mTypeHandler.ctype2asttype(loc, cType);
				final String tmpName = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, cType);
				final VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpName, type, loc);
				decl.add(tVarDecl);
				auxVars.put(tVarDecl, loc);

				returnValue = new RValue(new IdentifierExpression(loc, tmpName), cType);
				mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(), stmt);
				
				assert (isAuxVarMapcomplete(main.mNameHandler, decl, auxVars));
				return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
			}
		}
		if (methodName.equals("printf")) {
			// skip if parent of parent is CompoundStatement
			// otherwise, replace by havoced variable
			if (node.getParent().getParent() instanceof IASTCompoundStatement) {
				return new SkipResult();
			}
			// 2015-11-05 Matthias: TODO check if int is reasonable here
			final CType returnType = new CPrimitive(CPrimitives.INT);
			final ASTType tempType = mTypeHandler.ctype2asttype(loc, returnType);
			final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, null);
			final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, tempType) });
			auxVars.put(tVarDecl, loc);
			decl.add(tVarDecl);
			stmt.add(new HavocStatement(loc, new VariableLHS[] { new VariableLHS(loc, tId) }));
			returnValue = new RValue(new IdentifierExpression(loc, tId), null);
			assert (isAuxVarMapcomplete(main.mNameHandler, decl, auxVars));
			return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
		}
//		this is a gcc-builtin function that helps with branch prediction, it always returns the first argument.
		if (methodName.equals("__builtin_expect")) { 
			return main.dispatch(node.getArguments()[0]);
		}
		
		if (methodName.equals("__builtin_memcpy") || methodName.equals("memcpy")) {

			assert node.getArguments().length == 3 : "wrong number of arguments";
			ExpressionResult dest = (ExpressionResult) main.dispatch(node.getArguments()[0]);
			dest = dest.switchToRValueIfNecessary(main, getMemoryHandler(), mStructHandler, loc);
			main.mCHandler.convert(loc, dest, new CPointer(new CPrimitive(CPrimitives.VOID)));
			ExpressionResult src = (ExpressionResult) main.dispatch(node.getArguments()[1]);
			src = src.switchToRValueIfNecessary(main, getMemoryHandler(), mStructHandler, loc);
			main.mCHandler.convert(loc, src, new CPointer(new CPrimitive(CPrimitives.VOID)));
			ExpressionResult size = (ExpressionResult) main.dispatch(node.getArguments()[2]);
			size = size.switchToRValueIfNecessary(main, getMemoryHandler(), mStructHandler, loc);
			main.mCHandler.convert(loc, size, mTypeSizeComputer.getSize_T());
			
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(dest, src, size);
			
			final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MEMCPYRES, dest.lrVal.getCType());
			final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], 
					new VarList[] { new VarList(loc, new String[] { tId }, main.mTypeHandler.constructPointerType(loc)) });
			result.decl.add(tVarDecl);
			result.auxVars.put(tVarDecl, loc);		
			
			final Statement call = getMemoryHandler().constructMemcpyCall(loc, dest.lrVal.getValue(), 
					src.lrVal.getValue(), size.lrVal.getValue(), tId);
			result.stmt.add(call);
			result.lrVal = new RValue(new IdentifierExpression(loc, tId), 
					new CPointer(new CPrimitive(CPrimitives.VOID)));

			// add required information to function handler.
			if (!getFunctionHandler().getCallGraph().containsKey(MemoryModelDeclarations.C_Memcpy.getName())) {
				getFunctionHandler().getCallGraph().put(MemoryModelDeclarations.C_Memcpy.getName(), new LinkedHashSet<String>());
			}
			if (!getFunctionHandler().getModifiedGlobals().containsKey(MemoryModelDeclarations.C_Memcpy.getName())) {
				getFunctionHandler().getModifiedGlobals().put(MemoryModelDeclarations.C_Memcpy.getName(), new LinkedHashSet<String>());
			}
			getFunctionHandler().getCallGraph().get(getFunctionHandler().getCurrentProcedureID()).add(MemoryModelDeclarations.C_Memcpy.getName());
			
			return result;
		}
		
		if (methodName.equals("__builtin_object_size")) {
			main.warn(loc, "used trivial implementation of __builtin_object_size");
			final CPrimitive cType = new CPrimitive(CPrimitives.INT);
			final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO);
			return new ExpressionResult(new RValue(zero, cType));
		}
		
		if (methodName.equals("nan") || methodName.equals("nanf") || methodName.equals("nanl")) {
			
			return mExpressionTranslation.createNanOrInfinity(loc, methodName);
		}
		
		if (methodName.equals("__builtin_nan") || methodName.equals("__builtin_nanf") || methodName.equals("__builtin_nanl")
				|| methodName.equals("__builtin_inff")) {
			final String functionName = methodName.substring(methodName.length() - 4);
			return mExpressionTranslation.createNanOrInfinity(loc, functionName);
		}
		
		/*
		 * builtin_prefetch according to https://gcc.gnu.org/onlinedocs/gcc-3.4.5/gcc/Other-Builtins.html (state: 5.6.2015)
		 * triggers the processor to load something into cache, does nothing else
		 * is void thus has no return value
		 */
		if (methodName.equals("__builtin_prefetch") || 
				methodName.equals("__builtin_va_start") ||
				methodName.equals("__builtin_va_end") ||
				methodName.equals("__builtin_return_address")) {
			main.warn(loc, "ignored call to " + methodName);
			return new SkipResult();
		}

		if (methodName.equals("abort")) {
			stmt.add(new AssumeStatement(loc, new BooleanLiteral(loc, false)));
			return new ExpressionResult(stmt, null, decl, auxVars, overappr);
		}

		return super.visit(main, node);
	}

	
	@Override
	public Result visit(Dispatcher main, IASTIdExpression node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		if (node.getName().toString().equals("null")) {
			return new ExpressionResult(
					new RValue(mExpressionTranslation.constructNullPointer(loc),
					new CPointer(new CPrimitive(CPrimitives.VOID))));
		}
		if (node.getName().toString().equals("__PRETTY_FUNCTION__")
				|| node.getName().toString().equals("__FUNCTION__")){
			final CType returnType = new CPointer(new CPrimitive(CPrimitives.CHAR));
			final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, returnType);
			final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, main.mTypeHandler.constructPointerType(loc)) });
			final RValue rvalue = new RValue(new IdentifierExpression(loc, tId), returnType);
			final ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			auxVars.put(tVarDecl, loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, auxVars);
		}
		return super.visit(main, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTASMDeclaration node) {
		//workaround for now: ignore inline assembler instructions
		return new SkipResult();
	}

}
