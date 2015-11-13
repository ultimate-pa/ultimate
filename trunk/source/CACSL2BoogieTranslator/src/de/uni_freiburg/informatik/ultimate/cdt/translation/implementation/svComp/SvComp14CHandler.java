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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.IntegerTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
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
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;

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

	/**
	 * Constructor.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param bitvectorTranslation 
	 */
	public SvComp14CHandler(Dispatcher main, CACSL2BoogieBacktranslator backtranslator, 
			Logger logger, ITypeHandler typeHandler, boolean bitvectorTranslation) {
		super(main, backtranslator, false, logger, typeHandler, bitvectorTranslation);
	}

	//
	// __VERIFIER_assume(EXPR) && skip VERIFIER_nondet_X()
	//

	@Override
	public Result visit(Dispatcher main, IASTFunctionCallExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		if (!(node.getFunctionNameExpression() instanceof IASTIdExpression))
			return super.visit(main, node);
		IASTIdExpression astIdExpression = (IASTIdExpression) node.getFunctionNameExpression();
		String methodName = astIdExpression.getName().toString();

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
		LRValue returnValue = null;
		
		if (methodName.equals("pthread_create")) {
			throw new UnsupportedSyntaxException(loc, "we do not support pthread");
		}
		if (methodName.equals(ERROR_STRING)) {
			boolean checkSvcompErrorfunction = 
					main.mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SVCOMP_ERRORFUNCTION);
			if (checkSvcompErrorfunction) {
				Check check = new Check(Spec.ERROR_Function);
				AssertStatement assertStmt = new AssertStatement(loc, new BooleanLiteral(loc,
						new InferredType(Type.Boolean), false));
				check.addToNodeAnnot(assertStmt);
				stmt.add(assertStmt);
			} 
			return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
		}
		if (methodName.equals(ASSUME_STRING)) {
			ArrayList<Expression> args = new ArrayList<Expression>();
			for (IASTInitializerClause inParam : node.getArguments()) {
				ExpressionResult in = ((ExpressionResult) main.dispatch(inParam)).switchToRValueIfNecessary(main,
						mMemoryHandler, mStructHandler, loc);
				if (in.lrVal.getValue() == null) {
					String msg = "Incorrect or invalid in-parameter! " + loc.toString();
					throw new IncorrectSyntaxException(loc, msg);
				}
				in.rexIntToBoolIfNecessary(loc, m_ExpressionTranslation);
				args.add(in.lrVal.getValue());
				stmt.addAll(in.stmt);
				decl.addAll(in.decl);
				auxVars.putAll(in.auxVars);
				overappr.addAll(in.overappr);
			}
			assert args.size() == 1; // according to SV-Comp specification!
			for (Expression a : args) {
//			could just take the first as there is only one, but it's so easy to make it more general..
				stmt.add(new AssumeStatement(loc, a));
			}
			assert (isAuxVarMapcomplete(main, decl, auxVars));
			return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
		}
		for (String t : NONDET_TYPE_STRINGS)
			if (methodName.equals(NONDET_STRING + t)) {
				
				CType cType;
				switch (t) {
				case "_Bool":
				case "bool":
					cType = new CPrimitive(PRIMITIVE.BOOL);
					break;
				case "char":
					cType = new CPrimitive(PRIMITIVE.CHAR);
					break;
				case "float":
					cType = new CPrimitive(PRIMITIVE.FLOAT);
					throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), "we do not support floats");
//					break;
				case "double":
					cType = new CPrimitive(PRIMITIVE.DOUBLE);
					throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), "we do not support floats");
//					break;
				case "size_t":
				case "int":
					cType = new CPrimitive(PRIMITIVE.INT);
					break;
				case "loff_t":
				case "long":
					cType = new CPrimitive(PRIMITIVE.LONG);
					break;
				case "short":
					cType = new CPrimitive(PRIMITIVE.SHORT);
					break;
				case "pchar":
					cType = new CPointer(new CPrimitive(PRIMITIVE.CHAR));
					break;
				case "pointer":
//					NamedType boogiePointerType = new NamedType(null, new InferredType(Type.Struct), SFO.POINTER,
//							new ASTType[0]);
//					type = boogiePointerType;
					cType = new CPointer(new CPrimitive(PRIMITIVE.VOID));
					break;
				case "uchar":
					cType = new CPrimitive(PRIMITIVE.UCHAR);
					break;
				case "unsigned":
				case "uint":
					cType = new CPrimitive(PRIMITIVE.UINT);
					break;
				case "ulong":
					cType = new CPrimitive(PRIMITIVE.ULONG);
					break;
				case "ushort":
					cType = new CPrimitive(PRIMITIVE.USHORT);
					break;
				default:
					throw new AssertionError("unknown type " + t);
				}
				ASTType type = mTypeHandler.ctype2asttype(loc, cType);
				String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET, cType);
				VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpName, type, loc);
				decl.add(tVarDecl);
				auxVars.put(tVarDecl, loc);

				returnValue = new RValue(new IdentifierExpression(loc, tmpName), cType);
				m_ExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(), stmt);
				
				assert (isAuxVarMapcomplete(main, decl, auxVars));
				return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
			}
		if (methodName.equals("printf")) {
			// skip if parent of parent is CompoundStatement
			// otherwise, replace by havoced variable
			if (node.getParent().getParent() instanceof IASTCompoundStatement) {
				return new SkipResult();
			}
			// 2015-11-05 Matthias: TODO check if int is reasonable here
			CType returnType = new CPrimitive(PRIMITIVE.INT);
			ASTType tempType = mTypeHandler.ctype2asttype(loc, returnType);
			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET, null);
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, tempType) });
			auxVars.put(tVarDecl, loc);
			decl.add(tVarDecl);
			stmt.add(new HavocStatement(loc, new VariableLHS[] { new VariableLHS(loc, tId) }));
			returnValue = new RValue(new IdentifierExpression(loc, tId), null);
			assert (isAuxVarMapcomplete(main, decl, auxVars));
			return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
		}
//		this is a gcc-builtin function that helps with branch prediction, it always returns the first argument.
		if (methodName.equals("__builtin_expect")) { 
			return main.dispatch(node.getArguments()[0]);
		}
		
		if (methodName.equals("__builtin_memcpy")) {
			((CHandler) main.cHandler).mMemoryHandler.setDeclareMemCpy();

			assert node.getArguments().length == 3;
			ExpressionResult destRex = (ExpressionResult) main.dispatch(node.getArguments()[0]);
			ExpressionResult srcRex = (ExpressionResult) main.dispatch(node.getArguments()[1]);
			ExpressionResult sizeRex = (ExpressionResult) main.dispatch(node.getArguments()[2]);
			
			destRex = destRex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			srcRex = srcRex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			sizeRex = sizeRex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			
			stmt.addAll(destRex.stmt);
			stmt.addAll(srcRex.stmt);
			stmt.addAll(sizeRex.stmt);
			decl.addAll(destRex.decl);
			decl.addAll(srcRex.decl);
			decl.addAll(sizeRex.decl);
			auxVars.putAll(destRex.auxVars);
			auxVars.putAll(srcRex.auxVars);
			auxVars.putAll(sizeRex.auxVars);
			overappr.addAll(destRex.overappr);
			overappr.addAll(srcRex.overappr);
			overappr.addAll(sizeRex.overappr);		

			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MEMCPYRES, destRex.lrVal.getCType());
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, main.typeHandler.constructPointerType(loc)) });
			decl.add(tVarDecl);
			auxVars.put(tVarDecl, loc);		
			
			Statement call = new CallStatement(loc, false, new VariableLHS[] { new VariableLHS(loc, tId) }, SFO.MEMCPY, 
					new Expression[] { destRex.lrVal.getValue(), srcRex.lrVal.getValue(), sizeRex.lrVal.getValue() });
			stmt.add(call);

			// add required information to function handler.
			if (!mFunctionHandler.getCallGraph().containsKey(SFO.MEMCPY)) {
				mFunctionHandler.getCallGraph().put(SFO.MEMCPY, new LinkedHashSet<String>());
			}
			if (!mFunctionHandler.getModifiedGlobals().containsKey(SFO.MEMCPY)) {
				mFunctionHandler.getModifiedGlobals().put(SFO.MEMCPY, new LinkedHashSet<String>());
			}
			mFunctionHandler.getCallGraph().get(mFunctionHandler.getCurrentProcedureID()).add(SFO.MEMCPY);
			
			return new ExpressionResult(stmt, new RValue(new IdentifierExpression(loc, tId), 
					destRex.lrVal.getCType()), decl, auxVars, overappr);
		}
		
		if (methodName.equals("__builtin_object_size")) {
			main.warn(loc, "used trivial implementation of __builtin_object_size");
			return new ExpressionResult(new RValue(new IntegerLiteral(loc, SFO.NR0), 
					new CPrimitive(PRIMITIVE.INT)));
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
		ILocation loc = LocationFactory.createCLocation(node);
		if (node.getName().toString().equals("null")) {
			return new ExpressionResult(
					new RValue(mMemoryHandler.constructNullPointer(loc),
					new CPointer(new CPrimitive(PRIMITIVE.VOID))));
		}
		if (node.getName().toString().equals("__PRETTY_FUNCTION__")
				|| node.getName().toString().equals("__FUNCTION__")){
			CType returnType = new CPointer(new CPrimitive(PRIMITIVE.CHAR));
			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET, returnType);
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, main.typeHandler.constructPointerType(loc)) });
			RValue rvalue = new RValue(new IdentifierExpression(loc, tId), returnType);
			ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
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
