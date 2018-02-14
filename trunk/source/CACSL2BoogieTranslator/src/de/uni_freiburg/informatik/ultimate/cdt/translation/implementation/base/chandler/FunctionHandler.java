/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PRDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UndeclaredFunctionException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.LinkedHashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Class that handles translation of functions.
 *
 * Note about modifies clauses:
 *  <li> when an assignment is made, to a global variable, this must be registered with the function handler
 *    (via/addModifies..)
 *  <li> when a call is made, this must be registered with the function handler (via registerCall..)
 *     at the end of translation the modifies clauses are updated according to the call graph and the modifications
 *     from each procedure
 *
 * @author Markus Lindenmann
 * @date 12.10.2012
 * @author Alexander Nutz
 */
public class FunctionHandler {

	private final Map<String, ProcedureInfo> mProcedureNameToProcedureInfo;
	private final LinkedHashRelation<ProcedureInfo, ProcedureInfo> mInverseCallGraph;

	private ProcedureInfo mCurrentProcedureInfo;

	/**
	 * Methods that have been called before they were declared. These methods need a special treatment, as they are
	 * assumed to be returning int!
	 */
	private final Set<ProcedureInfo> mMethodsCalledBeforeDeclared;

	/**
	 * Herein the function Signatures (as a CFunction) are stored for which a boogie procedure has to be created in the
	 * postProcessor that deals with the function pointer calls that can happen.
	 */
	private final LinkedHashSet<ProcedureSignature> mFunctionSignaturesThatHaveAFunctionPointer;

	private final ExpressionTranslation mExpressionTranslation;

	/**
	 * Constructor.
	 *
	 * @param expressionTranslation
	 * @param typeSizeComputer
	 * @param checkMemoryLeakAtEndOfMain
	 */
	public FunctionHandler(final ExpressionTranslation expressionTranslation,
			final TypeSizeAndOffsetComputer typeSizeComputer) {
		mExpressionTranslation = expressionTranslation;

		mMethodsCalledBeforeDeclared = new LinkedHashSet<>();

		mProcedureNameToProcedureInfo = new LinkedHashMap<>();
		mInverseCallGraph = new LinkedHashRelation<>();

		mFunctionSignaturesThatHaveAFunctionPointer = new LinkedHashSet<>();
	}

	/**
	 * This is called from SimpleDeclaration and handles a C function declaration.
	 *
	 * The effects are: - the declaration is stored to FunctionHandler.procedures (which stores all Boogie procedure
	 * declarations - procedureTo(Return/Param)CType memebers are updated
	 *
	 * The returned result is empty (ResultSkip).
	 *
	 * @param cDec
	 *            the CDeclaration of the function that was computed by visit SimpleDeclaration
	 * @param loc
	 *            the location of the FunctionDeclarator
	 */
	public Result handleFunctionDeclarator(final Dispatcher main, final ILocation loc, final List<ACSLNode> contract,
			final CDeclaration cDec) {
		final String methodName = cDec.getName();
		final CFunction funcType = (CFunction) cDec.getType();

		registerProcedureDeclaration(main, loc, contract, methodName, funcType);

		return new SkipResult();
	}

	/**
	 * Handles translation of IASTFunctionDefinition.
	 * <p>
	 * Notes about the architecture:
	 * <ul>
	 *  <li> this method translates a function definition, as opposed to a declaration, so it has has body
	 *  <li> the Result that is returned by this method is a Boogie procedure <b>implementation</b>
	 *  <li> we also store a separate Boogie procedure <b>declaration</b> for each procedure
	 *  <li> the procedure declarations are managed in this class, they are added to the Boogie program during post
	 *   processing (i.e. at the end of CHandler.visit(IASTTranslationUnit ..) )
	 *  <li> closing the modifies clauses transitively will be done during post processing, it only modifies the
	 *    declarations
	 * </ul>
	 * <p>
	 * Note that a C function definition may have an ACSL specification while a Boogie procedure implementation does not
	 * have a specification (right?). Therefore we have to add any ACSL specs to the procedures member where the
	 * (Boogie) function declarations are stored.
	 * <p>
	 * The Result contains the Boogie procedure implementation.
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node to translate.
	 * @param contract
	 * @return the translation result.
	 */
	public Result handleFunctionDefinition(final Dispatcher main, final MemoryHandler memoryHandler,
			final IASTFunctionDefinition node, final CDeclaration cDec, final List<ACSLNode> contract) {

		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final String definedProcName = cDec.getName();

		final ProcedureInfo definedProcInfo = getOrConstructProcedureInfo(definedProcName);

		beginProcedureScope(main, definedProcInfo);

		final CType returnCType = ((CFunction) cDec.getType()).getResultType();
		final boolean returnTypeIsVoid =
				returnCType instanceof CPrimitive && ((CPrimitive) returnCType).getType() == CPrimitives.VOID;

//		updateCFunction(procName, returnCType, null, null, false);
		definedProcInfo.updateCFunction(returnCType, null, null, false);

		VarList[] in = processInParams(main, loc, (CFunction) cDec.getType(), definedProcInfo);
		if (isInParamVoid(in)) {
			// in-parameter is "void", as in "int foo(void) .." we normalize this to an empty list of in-parameters
			in = new VarList[0];
		}


		// There is only one return parameter in C, so this array always has size 1.
		VarList[] out = new VarList[1];
		final ASTType type = main.mTypeHandler.cType2AstType(loc, returnCType);

		if (returnTypeIsVoid) {
			// void, so there are no out vars
			out = new VarList[0];
		} else if (mMethodsCalledBeforeDeclared.contains(definedProcInfo)) {
			// defaulting to int, when a method is called that is only declared later
			final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);
			out[0] = new VarList(loc, new String[] { SFO.RES }, main.mTypeHandler.cType2AstType(loc, cPrimitive));
		} else {
			// "normal case"
			assert type != null;
			out[0] = new VarList(loc, new String[] { SFO.RES }, type);
		}
		Specification[] spec = makeBoogieSpecFromACSLContract(main, contract, definedProcInfo);

//		Procedure proc = mProcedures.get(methodName);

//		if (proc == null) {
		if (!definedProcInfo.hasDeclaration()) {
			/*
			 * we have not seen this procedure yet, make a new declaration, register the procedure
			 */
			final Attribute[] attr = new Attribute[0];
			final String[] typeParams = new String[0];
			final Procedure proc = new Procedure(loc, attr, definedProcName, typeParams, in, out, spec, null);
//			if (mProcedures.containsKey(methodName)) {
//				final String msg =
//						"Duplicated method identifier: " + methodName + ". C does not support function overloading!";
//				throw new IncorrectSyntaxException(loc, msg);
//			}
//			mProcedures.put(methodName, proc);
			definedProcInfo.setDeclaration(proc);
		} else {
			// check declaration against its implementation

			Procedure procDecl = definedProcInfo.getDeclaration();

			VarList[] declIn = procDecl.getInParams();
			boolean checkInParams = true;
			if (in.length != procDecl.getInParams().length || out.length != procDecl.getOutParams().length
					|| isInParamVoid(procDecl.getInParams())) {
				if (procDecl.getInParams().length == 0) {
					// the implementation can have 0 to n in parameters!
					// do not check, but use the in params of the implementation
					// as we will take the ones of the implementation anyway
					checkInParams = false;
					declIn = in;
//				} else if (isInParamVoid(proc.getInParams()) && (in.length == 0 || isInParamVoid(in))) {
//					declIn = new VarList[0];
//					in = new VarList[0];
//					checkInParams = false;
				} else {
					final String msg = "Implementation does not match declaration!";
					throw new IncorrectSyntaxException(loc, msg);
				}
			}

			if (checkInParams) {
				final ASTTypeComparisonVisitor comparer = new ASTTypeComparisonVisitor();

				for (int i = 0; i < in.length; i++) {
					final boolean isSimilar = comparer.isSimilar(in[i], procDecl.getInParams()[i]);
					if (!isSimilar) {
						final String msg = "Implementation does not match declaration! "
								+ "Type missmatch on in-parameters! " + in.length + " arguments, "
								+ procDecl.getInParams().length + " parameters, " + "first missmatch at position " + i
								+ ", " + "argument type " + BoogiePrettyPrinter.print(in[i].getType()) + ", param type "
								+ BoogiePrettyPrinter.print(procDecl.getInParams()[i]);
						throw new IncorrectSyntaxException(loc, msg);
					}
				}
			}

			// combine the specification from the definition with the one from
			// the declaration
			final List<Specification> specFromDec = Arrays.asList(procDecl.getSpecification());
			final ArrayList<Specification> newSpecs = new ArrayList<>(Arrays.asList(spec));
			newSpecs.addAll(specFromDec);
			spec = newSpecs.toArray(new Specification[newSpecs.size()]);

			procDecl = new Procedure(procDecl.getLocation(), procDecl.getAttributes(), procDecl.getIdentifier(), procDecl.getTypeParams(),
					declIn, procDecl.getOutParams(), spec, null);

			definedProcInfo.resetDeclaration(procDecl);
//			mProcedures.put(methodName, procDecl);
		}

		/*
		 * one more transformation of the declaration:
		 */
		{
			final Procedure proc = definedProcInfo.getDeclaration();
			final Procedure declWithCorrectlyNamedInParams = new Procedure(proc.getLocation(), proc.getAttributes(),
					proc.getIdentifier(), proc.getTypeParams(), in, proc.getOutParams(), proc.getSpecification(), null);
//			mCurrentProcedure = declWithCorrectlyNamedInParams;
			definedProcInfo.resetDeclaration(declWithCorrectlyNamedInParams);
			// mCurrentProcedureIsVoid = returnTypeIsVoid;
//			final String procId = mCurrentProcedure.getIdentifier();
		}

//		mCurrentProcedureInfo = currentProcInfo;

//		addModifiedGlobalEntry(procName);
//		addCallGraphNode(procName);

		/*
		 * The structure is as follows:
		 *  <li> Preprocessing of the method body: - add new variables for parameters - havoc them - etc. (1)
		 *  <li> dispatch body (2)
		 *  <li> handle mallocs (3)
		 *  <li> add statements and declarations to new body (4)
		 */
		ArrayList<Statement> stmts = new ArrayList<>();
		final ArrayList<Declaration> decls = new ArrayList<>();
		// 1)
		handleFunctionsInParams(main, loc, memoryHandler, decls, stmts, node);
		// 2)
		final ExpressionResult bodyResult = (ExpressionResult) main.dispatch(node.getBody());
		decls.addAll(bodyResult.mDecl);
		stmts.addAll(bodyResult.mStmt);

		// 3) ,4)
		stmts = ((CHandler) main.mCHandler).updateStmtsAndDeclsAtScopeEnd(main, decls, stmts);

		final Body body = new Body(loc, decls.toArray(new VariableDeclaration[decls.size()]),
				stmts.toArray(new Statement[stmts.size()]));

//		proc = mCurrentProcedure;
		final Procedure proc = definedProcInfo.getDeclaration();
		// Implementation -> Specification always null!
		final Procedure impl = new Procedure(loc, proc.getAttributes(), definedProcName, proc.getTypeParams(), in,
				proc.getOutParams(), null, body);

		// not sure if this is needed..
		definedProcInfo.setImplementation(impl);

//		mCurrentProcedure = null;
		endProcedureScope(main);

		return new Result(impl);
	}

	private void beginProcedureScope(final Dispatcher main, final ProcedureInfo currentProcInfo) {
		mCurrentProcedureInfo = currentProcInfo;
		main.mCHandler.beginScope();
	}

	private void endProcedureScope(final Dispatcher main) {
		mCurrentProcedureInfo = null;
		main.mCHandler.endScope();
	}

	/**
	 * Announce the use of a procedure to the FunctionHandler
	 * @param methodName
	 */
	public void registerProcedure(final String methodName) {
		getOrConstructProcedureInfo(methodName);
	}

	public void registerProcedureDeclaration(final String procName, final Procedure declaration) {
		final ProcedureInfo procInfo = getOrConstructProcedureInfo(procName);
		if (procInfo.hasDeclaration()) {
			throw new IllegalStateException("procedure already has a declaration, this is unexpected");
		}
		procInfo.setDeclaration(declaration);
	}

	private ProcedureInfo getOrConstructProcedureInfo(final String methodName) {

		ProcedureInfo result = mProcedureNameToProcedureInfo.get(methodName);
		if (result == null) {
			result = new ProcedureInfo(methodName);
			mProcedureNameToProcedureInfo.put(methodName, result);
		}

		return result;
	}

	/**
	 * expects that we have already constructed a ProcedureInfo for the given name
	 *
	 * @param procName
	 * @return
	 */
	private ProcedureInfo getProcedureInfo(final String procName) {
		final ProcedureInfo result = mProcedureNameToProcedureInfo.get(procName);
		if (result == null) {
			throw new IllegalArgumentException("a procedure of the given name is not yet known " + procName);
		}
		return result;
	}

	/**
	 * Handles translation of IASTFunctionCallExpression.
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param memoryHandler
	 *            a reference to the memory Handler.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleFunctionCallExpression(final Dispatcher main, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final ILocation loc, final IASTExpression functionName,
			final IASTInitializerClause[] arguments) {
		if (!(functionName instanceof IASTIdExpression)) {
			return handleFunctionPointerCall(loc, main, memoryHandler, structHandler, functionName, arguments);
		}
		final String methodName = ((IASTIdExpression) functionName).getName().toString();

		if (main.mCHandler.getSymbolTable().containsCSymbol(methodName)) {
			return handleFunctionPointerCall(loc, main, memoryHandler, structHandler, functionName, arguments);
		}

		return handleFunctionCallGivenNameAndArguments(main, memoryHandler, structHandler, loc, methodName, arguments);
	}

	/**
	 * Handles translation of return statements.
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleReturnStatement(final Dispatcher main, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final IASTReturnStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ArrayList<Overapprox> overApp = new ArrayList<>();
		// The ReturnValue could be empty!
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final VarList[] outParams = mCurrentProcedureInfo.getDeclaration().getOutParams();
		final ExpressionResult rExp = new ExpressionResult(stmt, null, decl, auxVars, overApp);
		// if (mMethodsCalledBeforeDeclared.contains(mCurrentProcedure.getIdentifier()) && mCurrentProcedureIsVoid) {
		if (mMethodsCalledBeforeDeclared.contains(mCurrentProcedureInfo)
				&& mCurrentProcedureInfo.getDeclaration().getOutParams().length == 0) {
			// void method that was assumed to be returning int! -> return int
			final String id = outParams[0].getIdentifiers()[0];
			final VariableLHS lhs = new VariableLHS(loc, id);
			final Statement havoc = new HavocStatement(loc, new VariableLHS[] { lhs });
			stmt.add(havoc);
		} else if (node.getReturnValue() != null) {
			final ExpressionResult returnValue = CTranslationUtil.convertExpressionListToExpressionResultIfNecessary(
					loc, main, main.dispatch(node.getReturnValue()));

			final ExpressionResult returnValueSwitched = returnValue.switchToRValueIfNecessary(main, loc);
			returnValueSwitched.rexBoolToIntIfNecessary(loc, mExpressionTranslation);

			// do some implicit casts
			final CType functionResultType =
					mCurrentProcedureInfo.getCType().getResultType();
			if (!returnValueSwitched.mLrVal.getCType().equals(functionResultType)
					&& functionResultType instanceof CPointer
					&& returnValueSwitched.mLrVal.getCType() instanceof CPrimitive
					&& returnValueSwitched.mLrVal.getValue() instanceof IntegerLiteral
					&& "0".equals(((IntegerLiteral) returnValueSwitched.mLrVal.getValue()).getValue())) {
				returnValueSwitched.mLrVal =
						new RValue(mExpressionTranslation.constructNullPointer(loc), functionResultType);
			}

			if (outParams.length == 0) {
				// void method which is returning something! We remove the
				// return value!
				final String msg = "This method is declared to be void, but returning a value!";
				main.syntaxError(loc, msg);
			} else if (outParams.length != 1) {
				final String msg = "We do not support several output parameters for functions";
				throw new UnsupportedSyntaxException(loc, msg);
			} else {
				final String id = outParams[0].getIdentifiers()[0];
				final VariableLHS[] lhs = new VariableLHS[] { new VariableLHS(loc, id) };
				// Ugly workaround: Apply the conversion to the result of the
				// dispatched argument. On should first construt a copy of returnValueSwitched
				main.mCHandler.convert(loc, returnValueSwitched, functionResultType);
				rExp.mLrVal = returnValueSwitched.mLrVal;
				final RValue castExprResultRVal = (RValue) rExp.mLrVal;
				stmt.addAll(returnValueSwitched.mStmt);
				decl.addAll(returnValueSwitched.mDecl);
				auxVars.putAll(returnValueSwitched.mAuxVars);
				overApp.addAll(returnValueSwitched.mOverappr);
				stmt.add(new AssignmentStatement(loc, lhs, new Expression[] { castExprResultRVal.getValue() }));
				// //assuming that we need no auxvars or overappr, here
			}
		}
		stmt.addAll(CHandler.createHavocsForAuxVars(auxVars));

		// we need to insert a free for each malloc of an auxvar before each return
		// frees are inserted in handleReturnStm
		for (final Entry<LocalLValueILocationPair, Integer> entry : memoryHandler.getVariablesToBeFreed().entrySet()) {
			if (entry.getValue() >= 1) {
				stmt.add(memoryHandler.getDeallocCall(main, this, entry.getKey().llv, entry.getKey().loc));
				stmt.add(new HavocStatement(loc, new VariableLHS[] { (VariableLHS) entry.getKey().llv.getLHS() }));
			}
		}

		stmt.add(new ReturnStatement(loc));
		return rExp;
	}

	/**
	 * This method is expected to be called from CHandler.visit(..TranslationUnit) after all procedures have been
	 * registered in the FunctionHandler.
	 * <p>
	 * Returns declarations for all procedures that will appear in the translated program. Ensures that the modifies
	 * clauses of all procedures are transitive with respect to the call graph.
	 * <p>
	 * Special case regarding memory models:
	 *  if one memory-array is included, all active memory arrays
	 * have to be included (f.i. we have procedure modifies memory_int, and memoryHandler.isFloatMMArray == true, and
	 * memoryHandler.isIntMMArray == true, memoryHandler.isPointerMMArray == false, then we have to add memory_real to
	 * the modifies clause of procedure
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @return procedure declarations
	 */
	public List<Declaration> computeFinalProcedureDeclarations(final Dispatcher main,
			final MemoryHandler memoryHandler) {
		final ProcedureInfo notDeclaredProcedure = isEveryCalledProcedureDeclared();
		if (notDeclaredProcedure != null) {
			throw new UndeclaredFunctionException(null, "a function that is called in the program "
					+ "is not declared in the program: " + notDeclaredProcedure.getProcedureName());
		}

		/**
		 * The base graph for the computation of strongly connected components (SCCs) is the inverse call graph.
		 * I.e., in the sense of this graph, the successors of a procedure are its callers.
		 */
		final ISuccessorProvider<ProcedureInfo> successorProvider = new ISuccessorProvider<ProcedureInfo>() {
			@Override
			public Iterator<ProcedureInfo> getSuccessors(final ProcedureInfo node) {
				return mInverseCallGraph.getImage(node).iterator();
			}
		};

		final int numberOfAllNodes = mProcedureNameToProcedureInfo.size();
		final Set<ProcedureInfo> startNodes = new HashSet<>(mProcedureNameToProcedureInfo.values());
		final DefaultSccComputation<ProcedureInfo> dssc =
				new DefaultSccComputation<>(main.getLogger(), successorProvider, numberOfAllNodes, startNodes);

		/*
		 * Initialize the modified globals for each SCC with the union of each method's modified globals.
		 *  (within an SCC all procedure may call all others (possibly transitively) thus all must have the same
		 *   modifies clause contents)
		 */
		final LinkedHashRelation<StronglyConnectedComponent<ProcedureInfo>, VariableLHS> sccToModifiedGlobals
			= new LinkedHashRelation<>();
		for (final StronglyConnectedComponent<ProcedureInfo> scc : dssc.getSCCs()) {
			for (final ProcedureInfo procInfo : scc.getNodes()) {
				for (final VariableLHS modGlobal : procInfo.getModifiedGlobals()) {
					sccToModifiedGlobals.addPair(scc, modGlobal);
				}
			}
		}

		/*
		 * update the modified globals for the sccs according to the edges in the call graph that connect different
		 * SCCs
		 *
		 * algorithmic idea:
		 *  start with the leafs of the graph and propagate all modified globals back along call edges.
		 *  The frontier is where we have already propagated modified globals.
		 *
		 */
		final Deque<StronglyConnectedComponent<ProcedureInfo>> frontier = new ArrayDeque<>();
		frontier.addAll(dssc.getLeafComponents());
		while (!frontier.isEmpty()) {
			final StronglyConnectedComponent<ProcedureInfo> currentScc = frontier.pollFirst();

			/*
			 * Note that we have chosen the ISuccessorProvider for the SccComputation such that the caller is the
			 *  successor of the callee. (i.e., the successor relation is the inverse of the call graph)
			 */
			final Set<VariableLHS> currentSccModGlobals = sccToModifiedGlobals.getImage(currentScc);
			final Iterator<StronglyConnectedComponent<ProcedureInfo>> callers =
					dssc.getComponentsSuccessorsProvider().getSuccessors(currentScc);
			while (callers.hasNext()) {
				final StronglyConnectedComponent<ProcedureInfo> caller = callers.next();
				frontier.add(caller);

				for (final VariableLHS currentSccModGlobal : currentSccModGlobals) {
					sccToModifiedGlobals.addPair(caller, currentSccModGlobal);
				}
			}
		}

		// update the modifies clauses!
		final ArrayList<Declaration> updatedDeclarations = new ArrayList<>();
		for (final ProcedureInfo procInfo : mProcedureNameToProcedureInfo.values()) {
			final Procedure oldProcDecl = procInfo.getDeclaration();

			final String procedureName = procInfo.getProcedureName();
			final Specification[] oldSpec = oldProcDecl.getSpecification();
			final CACSLLocation loc = (CACSLLocation) oldProcDecl.getLocation();

			final Specification[] newSpec;
			if (procInfo.isModifiedGlobalsIsUsedDefined()) {
				// modifies clause is user defined --> leave the specification as is
				newSpec = oldSpec;
			} else {
//			    // case: !procInfo.isModifiedGlobalsIsUsedDefined()
				final Set<VariableLHS> currModClause =
						sccToModifiedGlobals.getImage(dssc.getNodeToComponents().get(procInfo));
				assert currModClause != null : "No modifies clause proc " + procedureName;

				procInfo.addModifiedGlobals(currModClause);

				newSpec = Arrays.copyOf(oldSpec, oldSpec.length + 1);

				{
					/*
					 * add missing heap arrays If the procedure modifies one heap array, we add all heap arrays. This is
					 * a workaround. We cannot add all procedures immediately, because we do not know all heap arrays in
					 * advance since they are added lazily on demand.
					 *
					 */
					final Collection<HeapDataArray> heapDataArrays = memoryHandler.getMemoryModel()
							.getDataHeapArrays(memoryHandler.getRequiredMemoryModelFeatures());
					if (containsOneHeapDataArray(currModClause, heapDataArrays)) {
						for (final HeapDataArray hda : heapDataArrays) {
//							currModClause.add(hda.getVariableName());
							procInfo.addModifiedGlobal(hda.getVariableLHS());
						}
					}
				}

				final VariableLHS[] modifyList = new VariableLHS[currModClause.size()];
				{
					int i = 0;
					for (final VariableLHS modifyEntry : currModClause) {
						modifyList[i++] = modifyEntry;//new VariableLHS(loc, modifyEntry);
					}
				}
				newSpec[oldSpec.length] = new ModifiesSpecification(loc, false, modifyList);
			}

			/*
			 *
			 */
			final Specification[] newSpecWithExtraEnsuresClauses;
			if (memoryHandler.getRequiredMemoryModelFeatures().isMemoryModelInfrastructureRequired() && (main
					.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_ALLOCATION_PURITY)
					|| (main.getCheckedMethod().equals(SFO.EMPTY) || main.getCheckedMethod().equals(procedureName)) && main
							.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_MEMORY_LEAK_IN_MAIN))) {
				// add a specification to check for memory leaks

//				final Expression vIe = new IdentifierExpression(loc, SFO.VALID);
				final Expression vIe = //ExpressionFactory.constructIdentifierExpression(loc, MemoryModelDeclarations  SFO.VALID);
						main.mCHandler.getMemoryHandler().getValidArray(loc);

				final int nrSpec = newSpec.length;
				final Check check = new Check(Check.Spec.MEMORY_LEAK);
				final ILocation ensLoc = LocationFactory.createLocation(loc, check);
				newSpecWithExtraEnsuresClauses = Arrays.copyOf(newSpec, nrSpec + 1);
				newSpecWithExtraEnsuresClauses[nrSpec] = new EnsuresSpecification(ensLoc, false,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, vIe,
								ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.OLD, vIe)));
				check.annotate(newSpecWithExtraEnsuresClauses[nrSpec]);
				if (main.getPreferences()
						.getBoolean(CACSLPreferenceInitializer.LABEL_SVCOMP_MEMTRACK_COMPATIBILITY_MODE)) {
					new Overapprox(Collections.singletonMap("memtrack", ensLoc))
						.annotate(newSpecWithExtraEnsuresClauses[nrSpec]);
				}
			} else {
				newSpecWithExtraEnsuresClauses = newSpec;
			}
			updatedDeclarations.add(new Procedure(loc, oldProcDecl.getAttributes(), procedureName, oldProcDecl.getTypeParams(),
					oldProcDecl.getInParams(), oldProcDecl.getOutParams(), newSpecWithExtraEnsuresClauses, null));
		}
		return updatedDeclarations;
	}

	private static boolean containsOneHeapDataArray(final Set<VariableLHS> modifySet,
			final Collection<HeapDataArray> heapDataArrays) {
		for (final HeapDataArray hda : heapDataArrays) {
			if (modifySet.contains(hda.getVariableLHS())) {
				return true;
			}
		}
		return false;
	}

	private Result handleFunctionCallGivenNameAndArguments(final Dispatcher main, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final ILocation loc, final String calleeName,
			final IASTInitializerClause[] arguments) {

		if (!hasProcedure(calleeName)) {
			// TODO (feb 18) -- this case is probably treated by below code somehow but i dont know how, yet
			throw new UnsupportedOperationException("TODO: handle case when a procedure is called before it is "
					+ "declared");
		}

		final ProcedureInfo calleeProcInfo = getProcedureInfo(calleeName);


		registerCall(mCurrentProcedureInfo, calleeProcInfo);

		final Procedure calleeProcDecl = calleeProcInfo.getDeclaration();
		assert calleeProcDecl != null : "unclear -- solve in conjunction with the exception directly above..";


		/*
		 * If in C a function is declared without input parameters, and no implementation has been given yet, the
		 * definitive signature is determined by the first call to the function.
		 */
		final boolean isCalleeSignatureNotYetDetermined =
				!calleeProcInfo.hasImplementation() && calleeProcDecl.getInParams().length == 0;
//				procDecl != null && procDecl.getBody() == null && procDecl.getInParams().length == 0;

		final IASTInitializerClause[] inParams = arguments;
		final CFunction cFunction = calleeProcInfo.getCType();
		if (cFunction != null && cFunction.takesVarArgs()) {

			/* (EDIT, Alexander Nutz, Feb 2018, this describes an old solution:)
			 * if the function has varArgs, we throw away all parameters that belong
			 * to the varArgs part and only keep the normal ones
			 */
//			final int noParameterWOVarArgs = cFunction.getParameterTypes().length;
//			inParams = new IASTInitializerClause[noParameterWOVarArgs];
//			System.arraycopy(arguments, 0, inParams, 0, noParameterWOVarArgs);
//			if (!main.getPreferences().getEnum(CACSLPreferenceInitializer.LABEL_MODE, TranslationMode.class)
//					.equals(TranslationMode.SV_COMP14) && inParams.length < arguments.length) {
			throw new UnsupportedSyntaxException(loc, "encountered a call to a var args function, var args are not "
					+ "supported at the moment");
//			}
		}

		/*
		 * Check if the parameters of the call match the signature given in the function declaration.
		 *  (there is no constraint if the declaration had no parameters given, and we have not seen the implementation)
		 */
		if (!isCalleeSignatureNotYetDetermined) {
			if (calleeProcDecl != null && inParams.length != calleeProcDecl.getInParams().length
					&& !(calleeProcDecl.getInParams().length == 1 && calleeProcDecl.getInParams()[0].getType() == null
					&& inParams.length == 0)) {
				throw new IncorrectSyntaxException(loc, "Function call has incorrect number of in-params: "
						+ calleeName);
			} else {
				// signature of the call and signature of the declaration match, do nothing
			}
		}

		// EDIT Feb 18: what does this mean??:
		// this means param of declaration is void and parameter
		// list of call is empty! --> OK

		/*
		 *  dispatch the inparams
		 */
		final ArrayList<Expression> translatedParams = new ArrayList<>();
//		final ArrayList<Statement> stmt = new ArrayList<>();
//		final ArrayList<Declaration> decl = new ArrayList<>();
//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
//		final ArrayList<Overapprox> overappr = new ArrayList<>();
		final ExpressionResultBuilder functionCallExpressionResultBuilder = new ExpressionResultBuilder();
		for (int i = 0; i < inParams.length; i++) {
			final IASTInitializerClause inParam = inParams[i];
			ExpressionResult in = (ExpressionResult) main.dispatch(inParam);

			if (in.mLrVal.getCType().getUnderlyingType() instanceof CArray) {
				// arrays are passed as pointers --> switch to RValue would make a boogie array..
				final CType valueType =
						((CArray) in.mLrVal.getCType().getUnderlyingType()).getValueType().getUnderlyingType();
				if (in.mLrVal instanceof HeapLValue) {
					in.mLrVal = new RValue(((HeapLValue) in.mLrVal).getAddress(), new CPointer(valueType));
				} else {
					in.mLrVal = new RValue(in.mLrVal.getValue(), new CPointer(valueType));
				}
			} else {
				in = in.switchToRValueIfNecessary(main, loc);
			}

			if (in.mLrVal.getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}

			if (isCalleeSignatureNotYetDetermined) {
				// add the current parameter to the procedure's signature
				calleeProcInfo.updateCFunction(null, null, new CDeclaration(in.mLrVal.getCType(), SFO.IN_PARAM + i),
						false);
			} else if (cFunction != null) {
				// we already know the parameters: do implicit casts and bool/int conversion
				CType expectedParamType = cFunction.getParameterTypes()[i].getType().getUnderlyingType();
				// bool/int conversion
				if (expectedParamType instanceof CPrimitive
						&& ((CPrimitive) expectedParamType).getGeneralType() == CPrimitiveCategory.INTTYPE
						|| expectedParamType instanceof CEnum) {
					in.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
				}
				if (expectedParamType instanceof CFunction) {
					// workaround - better: make this conversion already in declaration
					expectedParamType = new CPointer(expectedParamType);
				}
				if (expectedParamType instanceof CArray) {
					// workaround - better: make this conversion already in declaration
					expectedParamType = new CPointer(((CArray) expectedParamType).getValueType());
				}
				// implicit casts
				main.mCHandler.convert(loc, in, expectedParamType);
			}
			translatedParams.add(in.mLrVal.getValue());
			functionCallExpressionResultBuilder.addAllExceptLrValue(in);
		}

		if (isCalleeSignatureNotYetDetermined) {
			/*
			 * This call determined the signature of the called function (it was declared without any parameters)
			 * Reset the declaration in our data structures.
			 */
			final VarList[] procParams = new VarList[cFunction.getParameterTypes().length];
			for (int i = 0; i < procParams.length; i++) {
				procParams[i] = new VarList(loc, new String[] { cFunction.getParameterTypes()[i].getName() },
						((TypeHandler) main.mTypeHandler).cType2AstType(loc,
								cFunction.getParameterTypes()[i].getType()));
			}
			final Procedure newProc = new Procedure(calleeProcDecl.getLocation(), calleeProcDecl.getAttributes(),
					calleeProcDecl.getIdentifier(), calleeProcDecl.getTypeParams(), procParams,
					calleeProcDecl.getOutParams(), calleeProcDecl.getSpecification(), calleeProcDecl.getBody());
			calleeProcInfo.resetDeclaration(newProc);
		}

		return makeTheFunctionCallItself(main, loc, calleeName, functionCallExpressionResultBuilder, translatedParams);
	}

	/**
	 * Announces that the procedure that is currently being translated calls another procedure.
	 *
	 * @param callee
	 */
	public void registerCall(final String callee) {
		if (isGlobalScope()) {
			throw new IllegalStateException("attempting to register a call when in global scope");
		}
		registerCall(mCurrentProcedureInfo, getProcedureInfo(callee));
	}

	/**
	 * Announces that a procedure calls another procedure somewhere in the translated program.
	 *  (for example this updates the call graph accordingly)
	 *
	 * @param caller
	 * @param callee
	 */
	public void registerCall(final String caller, final String callee) {
		registerCall(getProcedureInfo(caller), getProcedureInfo(callee));
	}

	private void registerCall(final ProcedureInfo caller, final ProcedureInfo callee) {
		if (!callee.hasDeclaration()) {
			mMethodsCalledBeforeDeclared.add(callee);
		}

		mInverseCallGraph.addPair(callee, caller);
	}

	/**
	 * How we translate function pointers:
	 *  <li> every function f, that is used as a pointer in the C code gets a number #f
	 *  <li> a pointer variable that points to a function then has the value {base: -1, offset: #f}
	 *  <li> for every function f, that is used as a pointer, and that has a signature s, we introduce a
	 *    "dispatch-procedure" in Boogie for s
	 *  <li> the dispatch-procedure for s = t1 x t2 x ... x tn -> t has the signature t1 x t2 x ... x tn x fp -> t, i.e.,
	 *    it takes the normal arguments, and a function address. When called, it calls the procedure that corresponds
	 *    to the function address with the corresponding arguments and returns the returned value
	 *  <li> a call to a function pointer is then translated to a call to the dispatch-procedure with fitting signature
	 *    where the function pointer is given as additional argument
	 *  <li> note: when thinking about the function signatures, one has to keep in mind, the differences between C and
	 *    Boogie, here. For instance, different C-function-signatures may correspond to on Boogie procedure signature,
	 *    because a Boogie pointer does not know what it points to. Also, void types need special treatment as any
	 *    pointer can be used as a void-pointer The special method CType.isCompatibleWith() is used for this. <br>
	 *    --> the names of the different dispatch function have to precisely match the classification done by
	 *     {@link CType.isCompatibleWith(..)).
	 *
	 * @param loc
	 * @param main
	 * @param memoryHandler
	 * @param structHandler
	 * @param functionName
	 * @param arguments
	 * @return
	 */
	private Result handleFunctionPointerCall(final ILocation loc, final Dispatcher main,
			final MemoryHandler memoryHandler, final StructHandler structHandler, final IASTExpression functionName,
			final IASTInitializerClause[] arguments) {

		assert main instanceof PRDispatcher || ((MainDispatcher) main).getFunctionToIndex().size() > 0;
		final ExpressionResult funcNameRex = (ExpressionResult) main.dispatch(functionName);
		// RValue calledFuncRVal = (RValue) funcNameRex.switchToRValueIfNecessary(main, memoryHandler, structHandler,
		// loc).lrVal;
		CType calledFuncType = funcNameRex.mLrVal.getCType().getUnderlyingType();
		if (!(calledFuncType instanceof CFunction) && calledFuncType instanceof CPointer) {
			// .. because function pointers don't need to be dereferenced in
			// order to be called
			calledFuncType = ((CPointer) calledFuncType).pointsToType.getUnderlyingType();
		}
		assert calledFuncType instanceof CFunction : "We need to unpack it further, right?";
		CFunction calledFuncCFunction = (CFunction) calledFuncType;

		// check if the function is declared without parameters -- then the
		// signature is determined by the (first) call
		if (calledFuncCFunction.getParameterTypes().length == 0 && arguments.length > 0) {
			final CDeclaration[] paramDecsFromCall = new CDeclaration[arguments.length];
			for (int i = 0; i < arguments.length; i++) {
				final ExpressionResult rex = (ExpressionResult) main.dispatch(arguments[i]);
				paramDecsFromCall[i] = new CDeclaration(rex.mLrVal.getCType(), "#param" + i); // TODO:
				// SFO?
			}
			calledFuncCFunction = new CFunction(calledFuncCFunction.getResultType(), paramDecsFromCall,
					calledFuncCFunction.takesVarArgs());
		}

		// new Procedure()
		// functionSignaturesThatHaveAFunctionPointer = null;
		// TODO: use CType.isCompatibleWith instead of equals/set, make the name of the inserted procedure compatible to
		// isCompatibleWith
		// TODO: DD 2017-11-23: Could we remove this collection of unknown symbols if we had a complete function symbol
		// table (perhaps collected in a prerun?)?
		final ProcedureSignature procSig = new ProcedureSignature(main, calledFuncCFunction);
		mFunctionSignaturesThatHaveAFunctionPointer.add(procSig);

		// String procName = calledFuncCFunction.functionSignatureAsProcedureName();
		final String procName = procSig.toString();

		final CFunction cFuncWithFP = addFPParamToCFunction(calledFuncCFunction);

//		if (!mProcedures.containsKey(procName)) {
			registerProcedureDeclaration(main, loc, null, procName, cFuncWithFP);
//		}

		final IASTInitializerClause[] newArgs = new IASTInitializerClause[arguments.length + 1];
		System.arraycopy(arguments, 0, newArgs, 0, arguments.length);
		newArgs[newArgs.length - 1] = functionName;

		return handleFunctionCallGivenNameAndArguments(main, memoryHandler, structHandler, loc, procName, newArgs);
	}

	/**
	 * takes the contract (we got from CHandler) and translates it into an array of Boogie specifications (this needs to
	 * be called after the procedure parameters have been added to the symboltable)
	 *
	 * @param main
	 * @param contract
	 * @param methodName
	 * @return
	 */
	private Specification[] makeBoogieSpecFromACSLContract(final Dispatcher main, final List<ACSLNode> contract,
			final ProcedureInfo procInfo) {
//			final String methodName) {
		Specification[] spec;
		if (contract == null) {
			spec = new Specification[0];
		} else {
			final List<Specification> specList = new ArrayList<>();
			for (int i = 0; i < contract.size(); i++) {
				// retranslate ACSL specification needed e.g., in cases
				// where ids of function parameters differ from is in ACSL
				// expression
				final Result retranslateRes = main.dispatch(contract.get(i));
				assert retranslateRes instanceof ContractResult;
				final ContractResult resContr = (ContractResult) retranslateRes;
				specList.addAll(Arrays.asList(resContr.specs));
			}
			spec = specList.toArray(new Specification[specList.size()]);
			for (int i = 0; i < spec.length; i++) {
				if (spec[i] instanceof ModifiesSpecification) {
//					mModifiedGlobalsIsUserDefined.add(methodName);
					procInfo.setModifiedGlobalsIsUsedDefined(true);
					final ModifiesSpecification ms = (ModifiesSpecification) spec[i];
					final LinkedHashSet<VariableLHS> modifiedSet = new LinkedHashSet<>();
					for (final VariableLHS var : ms.getIdentifiers()) {
						modifiedSet.add(var);
					}
//					mModifiedGlobals.put(methodName, modifiedSet);
					procInfo.addModifiedGlobals(modifiedSet);
				}
			}

			main.mCHandler.clearContract(); // take care for behavior and
											// completeness
		}
		return spec;
	}

	/**
	 * Take the parameter information from the CDeclaration. Make a Varlist from it. Add the parameters to the
	 * symboltable. Also update procedureToParamCType member.
	 *
	 * @return
	 */
	private VarList[] processInParams(final Dispatcher main, final ILocation loc, final CFunction cFun,
			final ProcedureInfo procInfo) {
//			final String methodName) {
		final CDeclaration[] paramDecs = cFun.getParameterTypes();
		final VarList[] in = new VarList[paramDecs.length];
		for (int i = 0; i < paramDecs.length; ++i) {
			final CDeclaration currentParamDec = paramDecs[i];

			final ASTType currentParamType;
			if (currentParamDec.getType() instanceof CArray) {
				// arrays are passed as pointers in C -- so we pass a Pointer in Boogie
				currentParamType = main.mTypeHandler.constructPointerType(loc);
			} else {
				currentParamType = main.mTypeHandler.cType2AstType(loc, currentParamDec.getType().getUnderlyingType());
			}

			final String currentParamId = main.mNameHandler.getInParamIdentifier(currentParamDec.getName(),
					currentParamDec.getType());
			in[i] = new VarList(loc, new String[] { currentParamId }, currentParamType);

			final DeclarationInformation declInformation = new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM,
					procInfo.getProcedureName());

			main.mCHandler.getSymbolTable().put(currentParamDec.getName(),
					new SymbolTableValue(currentParamId, null, currentParamDec, declInformation, null, false));
		}
		procInfo.updateCFunction(null, paramDecs, null, false);
		return in;
	}

	/**
	 * Basic idea:
	 * For each of the procedure's input parameters we
	 * <li> create an auxiliary variable,
	 * <li> add code that initializes the auxiliary variable to the corresponding input parameter
	 *
	 * (note, alex, feb 18: I suppose this is because C allows changing of in parameters while Boogie does not, but
	 *  would have to look it up to be sure)
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param loc
	 *            the location
	 * @param decl
	 *            the declaration list to append to.
	 * @param stmt
	 *            the statement list to append to.
	 * @param parent
	 */
	private void handleFunctionsInParams(final Dispatcher main, final ILocation loc, final MemoryHandler memoryHandler,
			final ArrayList<Declaration> decl, final ArrayList<Statement> stmt, final IASTFunctionDefinition parent) {
		final VarList[] inparamVarListArray = mCurrentProcedureInfo.getDeclaration().getInParams();
		IASTNode[] paramDecs;
		if (inparamVarListArray.length == 0) {
			/*
			 * In C it is possible to write func(void) { ... } This results in the empty name. (alex: what is an empty
			 * name??)
			 */
			if (parent.getDeclarator() instanceof IASTStandardFunctionDeclarator) {
				assert ((IASTStandardFunctionDeclarator) parent.getDeclarator()).getParameters().length == 0
						|| ((IASTStandardFunctionDeclarator) parent.getDeclarator()).getParameters().length == 1 && ""
								.equals(((IASTStandardFunctionDeclarator) parent.getDeclarator()).getParameters()[0]
										.getDeclarator().getName().toString());

			}
			paramDecs = new IASTParameterDeclaration[0];
		} else {
			if (parent.getDeclarator() instanceof IASTStandardFunctionDeclarator) {
				paramDecs = ((IASTStandardFunctionDeclarator) parent.getDeclarator()).getParameters();
			} else if (parent.getDeclarator() instanceof ICASTKnRFunctionDeclarator) {
				paramDecs = ((ICASTKnRFunctionDeclarator) parent.getDeclarator()).getParameterDeclarations();
			} else {
				paramDecs = null;
				assert false : "are we missing a type of function declarator??";
			}
		}

		assert inparamVarListArray.length == paramDecs.length;
		for (int i = 0; i < paramDecs.length; ++i) {
			final VarList inparamVarList = inparamVarListArray[i];
			// final IASTParameterDeclaration paramDec = paramDecs[i];
			final IASTNode paramDec = paramDecs[i];
			for (final String bId : inparamVarList.getIdentifiers()) {
				final String cId = main.mCHandler.getSymbolTable().getCID4BoogieID(bId, loc);

				ASTType type = inparamVarList.getType();
				final CType cvar = main.mCHandler.getSymbolTable().get(cId, loc).getCVariable();

				// onHeap case for a function parameter means the parameter is
				// addressoffed in the function body
				boolean isOnHeap = false;
				if (main instanceof MainDispatcher) {
					isOnHeap = ((MainDispatcher) main).getVariablesForHeap().contains(paramDec);
				}

				// Copy of inparam that is writeable
				final String inparamAuxVarName = main.mNameHandler.getUniqueIdentifier(parent, cId, 0, isOnHeap, cvar);

				final DeclarationInformation inparamAuxVarDeclInfo = new DeclarationInformation(StorageClass.LOCAL,
						mCurrentProcedureInfo.getProcedureName());
				final BoogieType inParamAuxVarType = main.mCHandler.getBoogieTypeHelper()
						.getBoogieTypeForBoogieASTType(type);

				if (isOnHeap || cvar instanceof CArray) {
					type = main.mTypeHandler.constructPointerType(loc);
					((CHandler) main.mCHandler).addBoogieIdsOfHeapVars(inparamAuxVarName);
				}
				final VarList var = new VarList(loc, new String[] { inparamAuxVarName }, type);
				final VariableDeclaration inVarDecl =
						new VariableDeclaration(loc, new Attribute[0], new VarList[] { var });

				final VariableLHS tempLHS = new VariableLHS(loc, inparamAuxVarName);
//				final IdentifierExpression rhsId = new IdentifierExpression(loc, bId);
				final IdentifierExpression rhsId = ExpressionFactory.constructIdentifierExpression(loc,
						inParamAuxVarType, bId, inparamAuxVarDeclInfo);

				final ILocation igLoc = LocationFactory.createIgnoreLocation(loc);
				if (isOnHeap && !(cvar instanceof CArray)) {
					// we treat an array argument as a pointer -- thus no onHeap treatment here
					final LocalLValue llv = new LocalLValue(tempLHS, cvar, null);
					// malloc
					memoryHandler.addVariableToBeFreed(main, new LocalLValueILocationPair(llv, igLoc));
					// dereference
					final HeapLValue hlv = new HeapLValue(llv.getValue(), cvar, null);

					// convention (or rather an insight?): if a variable is put on heap or not, its ctype stays the same
					final ExpressionResult assign = ((CHandler) main.mCHandler).makeAssignment(main, igLoc, hlv,
							Collections.emptyList(),
							new ExpressionResultBuilder().setLrVal(new RValue(rhsId, cvar)).build());

					stmt.add(memoryHandler.getMallocCall(llv, igLoc));
					stmt.addAll(assign.mStmt);
				} else {
					stmt.add(
							new AssignmentStatement(igLoc, new LeftHandSide[] { tempLHS }, new Expression[] { rhsId }));
				}
				assert main.mCHandler.getSymbolTable().containsCSymbol(cId);

				// Overwrite the information in the symbolTable for cId, s.t. it
				// points to the locally declared variable.
				main.mCHandler.getSymbolTable().put(cId,
						new SymbolTableValue(inparamAuxVarName, inVarDecl, new CDeclaration(cvar, cId),
								inparamAuxVarDeclInfo, paramDec, false));
			}
		}
	}

//	/**
//	 * Update the map procedureToCFunctionType according to the given arguments If a parameter is null, the
//	 * corresponding value will not be changed. (for takesVarArgs, use "false" to change nothing).
//	 */
//	private static void updateCFunction(final ProcedureInfo procInfo, final CType returnType,
//			final CDeclaration[] allParamDecs,
//			final CDeclaration oneParamDec, final boolean takesVarArgs) {
//		final CFunction oldCFunction = procInfo.getCType();
//
////		final CType oldRetType = oldCFunction == null ? null : oldCFunction.getResultType();
//		final CType oldRetType = procInfo.hasCType() ? procInfo.getCType().getResultType() : null;
//		final CDeclaration[] oldInParams =
////				oldCFunction == null ? new CDeclaration[0] : oldCFunction.getParameterTypes();
//				procInfo.hasCType() ? procInfo.getCType().getParameterTypes() : new CDeclaration[0];
////		final boolean oldTakesVarArgs = oldCFunction == null ? false : oldCFunction.takesVarArgs();
//		final boolean oldTakesVarArgs = procInfo.hasCType() ? procInfo.getCType().takesVarArgs() : false;
//
//		CType newRetType = oldRetType;
//		CDeclaration[] newInParams = oldInParams;
//		final boolean newTakesVarArgs = oldTakesVarArgs || takesVarArgs;
//
//		if (allParamDecs != null) { // set a new parameter list
//			assert oneParamDec == null;
//			newInParams = allParamDecs;
//		} else if (oneParamDec != null) { // add a parameter to the list
//			assert allParamDecs == null;
//
//			final ArrayList<CDeclaration> ips = new ArrayList<>(Arrays.asList(oldInParams));
//			ips.add(oneParamDec);
//			newInParams = ips.toArray(new CDeclaration[ips.size()]);
//		}
//		if (returnType != null) {
//			newRetType = returnType;
//		}
//
//		procInfo.resetCType(new CFunction(newRetType, newInParams, newTakesVarArgs));
//	}

	/**
	 * Register a new procedure declaration in our internal data structures.
	 *
	 * @param contract
	 * 			allows to give null for empty contract
	 * @param funcType
	 * 			the signature of the corresponding C function
	 */
	private void registerProcedureDeclaration(final Dispatcher main, final ILocation loc, final List<ACSLNode> contract,
			final String methodName, final CFunction funcType) {
		final ProcedureInfo procInfo = getOrConstructProcedureInfo(methodName);

		// begin new scope for retranslation of ACSL specification
		main.mCHandler.beginScope();

		final VarList[] in = processInParams(main, loc, funcType, procInfo);

		// OUT VARLIST : only one out param in C
		VarList[] out = new VarList[1];

		final Attribute[] attr = new Attribute[0];
		final String[] typeParams = new String[0];
		Specification[] spec = makeBoogieSpecFromACSLContract(main, contract, procInfo);

		if (funcType.getResultType() instanceof CPrimitive
				&& ((CPrimitive) funcType.getResultType()).getType() == CPrimitives.VOID
				&& !(funcType.getResultType() instanceof CPointer)) {
//			if (mMethodsCalledBeforeDeclared.contains(methodName)) {
			if (mMethodsCalledBeforeDeclared.contains(procInfo)) {
				// this method was assumed to return int -> return int
				out[0] = new VarList(loc, new String[] { SFO.RES }, new PrimitiveType(loc, SFO.INT));
			} else {
				// void, so there are no out vars
				out = new VarList[0];
			}
		} else {
			// we found a type, so node is type ASTType
			final ASTType type = main.mTypeHandler.cType2AstType(loc, funcType.getResultType());
			out[0] = new VarList(loc, new String[] { SFO.RES }, type);
		}

		if (procInfo.hasDeclaration()) {
			// combine the specification from the definition with the one from
			// the declaration
			final List<Specification> specFromDef = Arrays.asList(procInfo.getDeclaration().getSpecification());
			final ArrayList<Specification> newSpecs = new ArrayList<>(Arrays.asList(spec));
			newSpecs.addAll(specFromDef);
			spec = newSpecs.toArray(new Specification[newSpecs.size()]);
			// TODO something else to take over for a declaration after the
			// definition?
		}
		final Procedure newDeclaration = new Procedure(loc, attr, procInfo.getProcedureName(), typeParams, in, out,
				spec, null);

		procInfo.resetDeclaration(newDeclaration);

		procInfo.updateCFunction(funcType.getResultType(), null, null, funcType.takesVarArgs());
		// end scope for retranslation of ACSL specification
		main.mCHandler.endScope();
	}

//	/**
//	 * Adds searchString to modifiedGlobals iff searchString is a global variable and the user has not defined a
//	 * modifies clause.
//	 *
//	 * @param main
//	 *            a reference to the main dispatcher.
//	 *
//	 * @param searchString
//	 *            = boogieVarName!
//	 * @param errLoc
//	 *            the location for possible errors!
//	 */
//	public void checkIfModifiedGlobal(final SymbolTable symbTab, final String searchString, final ILocation errLoc) {
//		String cName;
//		if (!symbTab.containsBoogieSymbol(searchString)) {
//			// temp variable!
//			return;
//		}
//		cName = symbTab.getCID4BoogieID(searchString, errLoc);
//		final String cId = mCurrentProcedure.getIdentifier();
//		final SymbolTableValue stValue = symbTab.get(cName, errLoc);
//		final CType cvar = stValue.getCVariable();
//		if (cvar != null && stValue.getCDecl().isStatic()) {
//			mModifiedGlobals.get(cId).add(searchString);
//			return;
//		}
//		if (mModifiedGlobalsIsUserDefined.contains(cId)) {
//			return;
//		}
//		final boolean isLocal;
//		if (searchString.equals(SFO.RES)) {
//			// this variable is reserved for the return variable and
//			// therefore local!
//			isLocal = true;
//		} else {
//			isLocal = !symbTab.get(cName, errLoc).isBoogieGlobalVar();
//		}
//		if (!isLocal) {
//			// the variable is not local but could be a formal parameter
//			if (!searchString.startsWith(SFO.IN_PARAM)) {
//				// variable is global!
//				mModifiedGlobals.get(cId).add(searchString);
//			} else {
//				assert false;
//			}
//		}
//	}

	/**
	 * Checks, whether all procedures that are being called in C, were eventually declared within the C program.
	 *
	 * @return null if all called procedures were declared, otherwise the identifier of one procedure that was called
	 *         but not declared.
	 */
	private ProcedureInfo isEveryCalledProcedureDeclared() {
		for (final ProcedureInfo s : mMethodsCalledBeforeDeclared) {
			if (!s.hasDeclaration()) {
				return s;
			}
		}
		return null;
	}

	void beginUltimateInitOrStart(final Dispatcher main, final ILocation loc, final String startOrInit) {
//		main.mCHandler.beginScope();


		final ProcedureInfo procInfo = getOrConstructProcedureInfo(startOrInit);

		beginProcedureScope(main, procInfo);
//		mCurrentProcedure = new Procedure(loc, new Attribute[0], startOrInit, new String[0], new VarList[0],
//				new VarList[0], new Specification[0], null);
//
//		final ProcedureInfo procInfo = getOrConstructProcedureInfo(startOrInit);
//		procInfo.setDeclaration(mCurrentProcedure);

//		mModifiedGlobals.put(mCurrentProcedure.getIdentifier(), new LinkedHashSet<String>());
		registerProcedureDeclaration(main, loc, null, startOrInit,
				new CFunction(new CPrimitive(CPrimitives.VOID), new CDeclaration[0], false));
	}

	/**
	 *
	 * @param main
	 * @param initDecl
	 * 		note this must be a pure declaration, i.e., its body must be null
	 * @param startOrInit
	 * @param calledProcedures
	 */
	void endUltimateInitOrStart(final Dispatcher main, final String startOrInit) {
//	void endUltimateInitOrStart(final Dispatcher main, final Procedure initDecl, final String startOrInit) {
//	void endUltimateInitOrStart(final Dispatcher main, final Procedure initDecl, final String startOrInit,
//			final Collection<String> calledProcedures) {
//		for (final String calledProcedure : calledProcedures) {
//			addCallGraphEdge(startOrInit, calledProcedure);
//		}

//		mProcedures.put(startOrInit, initDecl);
		// TODO: rethink this -- is this resetting only about modifies clause? if yes: shouldn't this be handled elsewhere?
		//  EDIT: indeed, updates to modifies clauses should be registered with the function handler
//		final ProcedureInfo procInfo = getProcedureInfo(startOrInit);
//		procInfo.resetDeclaration(initDecl);

//		mCurrentProcedureInfo = null;
//
//		main.mCHandler.endScope();
		endProcedureScope(main);
	}

	private static CFunction addFPParamToCFunction(final CFunction calledFuncCFunction) {
		final CDeclaration[] newCDecs = new CDeclaration[calledFuncCFunction.getParameterTypes().length + 1];
		for (int i = 0; i < newCDecs.length - 1; i++) {
			newCDecs[i] = calledFuncCFunction.getParameterTypes()[i];
		}
		// FIXME string to SFO..?
		newCDecs[newCDecs.length - 1] = new CDeclaration(new CPointer(new CPrimitive(CPrimitives.VOID)), "#fp");

		final CFunction cFuncWithFP = new CFunction(calledFuncCFunction.getResultType(), newCDecs, false);
		return cFuncWithFP;
	}

	/**
	 * FIXME: change the method name
	 *
	 * @param main
	 * @param loc
	 * @param methodName
	 * @param functionCallExpressionResultBuilder
	 * @param translatedParameters
	 * @return
	 */
	Result makeTheFunctionCallItself(final Dispatcher main, final ILocation loc, final String methodName,
			final ExpressionResultBuilder functionCallExpressionResultBuilder,
			final List<Expression> translatedParameters) {
		Expression returnedValue = null;
		Statement call;

		ProcedureInfo procInfo;

		if (hasProcedure(methodName)) {
			procInfo = mProcedureNameToProcedureInfo.get(methodName);
			final VarList[] outParamVarlists = procInfo.getDeclaration().getOutParams();

			if (outParamVarlists.length == 0) { // void
				// C has only one return statement -> no need for forall
				call = new CallStatement(loc, false, new VariableLHS[0], methodName,
						translatedParameters.toArray(new Expression[translatedParameters.size()]));
			} else if (outParamVarlists.length == 1) { // one return value
				final VariableLHS returnedValueAsLhs;
				final VariableDeclaration tmpVarDecl;
				{
					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.RETURNED, null);
					final BoogieType tmpBoogieType = main.mCHandler.getBoogieTypeHelper()
							.getBoogieTypeForBoogieASTType(outParamVarlists[0].getType());
					final DeclarationInformation tmpDeclInfo = new DeclarationInformation(StorageClass.LOCAL,
							mCurrentProcedureInfo.getProcedureName());

					//				returnedValue = new IdentifierExpression(loc, tmpId);
					returnedValue = ExpressionFactory.constructIdentifierExpression(loc, tmpBoogieType, tmpId,
							tmpDeclInfo);
					returnedValueAsLhs = ExpressionFactory.constructVariableLHS(loc, tmpBoogieType, tmpId, tmpDeclInfo);
					tmpVarDecl = SFO.getTempVarVariableDeclaration(tmpId, outParamVarlists[0].getType(), loc);
				}
//				final VariableDeclaration tmpVarDecl = SFO.getTempVarVariableDeclaration(tmpId,
//						outParamVarlists[0].getType(), loc);

				functionCallExpressionResultBuilder.putAuxVar(tmpVarDecl, loc);
				functionCallExpressionResultBuilder.addDeclaration(tmpVarDecl);

				call = new CallStatement(loc, false, new VariableLHS[] { returnedValueAsLhs }, methodName,
						translatedParameters.toArray(new Expression[translatedParameters.size()]));
			} else { // unsupported!
				// String msg = "Cannot handle multiple out params! "
				// + loc.toString();
				// throw new IncorrectSyntaxException(loc, msg);
				return null; // FIXME ..
			}
		} else {
			procInfo = getOrConstructProcedureInfo(methodName);
			mMethodsCalledBeforeDeclared.add(procInfo);

			final String longDescription = "Method was called before it was declared: '" + methodName
					+ "' unknown! Return value is assumed to be int ...";
			main.warn(loc, longDescription);
			final String ident = main.mNameHandler.getTempVarUID(SFO.AUXVAR.RETURNED, null);

//			returnedValue = new IdentifierExpression(loc, ident);
			returnedValue = ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT, ident,
					new DeclarationInformation(StorageClass.LOCAL, mCurrentProcedureInfo.getProcedureName()));

			// we don't know the CType of the returned value
			// we we INT
			final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);
			final VarList tempVar =
					new VarList(loc, new String[] { ident }, main.mTypeHandler.cType2AstType(loc, cPrimitive));
			final VariableDeclaration tmpVarDecl =
					new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });

			functionCallExpressionResultBuilder.putAuxVar(tmpVarDecl, loc);
			functionCallExpressionResultBuilder.addDeclaration(tmpVarDecl);

			final VariableLHS lhs = new VariableLHS(loc, ident);
			call = new CallStatement(loc, false, new VariableLHS[] { lhs }, methodName,
					translatedParameters.toArray(new Expression[translatedParameters.size()]));
		}
		functionCallExpressionResultBuilder.addStatement(call);

		final CType returnCType = mMethodsCalledBeforeDeclared.contains(procInfo) ? new CPrimitive(CPrimitives.INT)
				: procInfo.getCType().getResultType();
//				: mProcedureToCFunctionType.get(methodName).getResultType().getUnderlyingType();

		mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnedValue, returnCType,
				functionCallExpressionResultBuilder);

		assert CHandler.isAuxVarMapComplete(main.mNameHandler,
				functionCallExpressionResultBuilder.getDeclarations(),
				functionCallExpressionResultBuilder.getAuxVars());

		functionCallExpressionResultBuilder.setLrVal(new RValue(returnedValue, returnCType));

		return functionCallExpressionResultBuilder.build();
	}

	/**
	 * Checks a VarList for a specific pattern, that represents "void".
	 *
	 * @param in
	 *            the methods in-parameter list.
	 * @return true iff in represents void.
	 */
	private static final boolean isInParamVoid(final VarList[] in) {
		if (in.length > 0 && in[0] == null) {
			throw new IllegalArgumentException("In-param cannot be null!");
		}
		// convention (necessary probably only because of here):
		// typeHandler.ctype2boogietype yields "null" for
		// CPrimitive(PRIMITIVE.VOID)
		return in.length == 1 && in[0].getType() == null;
	}

	public Procedure getProcedureDeclaration(final String procedureName) {
		final ProcedureInfo procInfo = getProcedureInfo(procedureName);
		if (!procInfo.hasDeclaration()) {
			throw new IllegalArgumentException("a procedure of the requested name is not yet known: " + procedureName);
		}
		return procInfo.getDeclaration();
	}

	/**
	 *
	 * @return true iff we (the translation) are currently in global scope. (We are in global scope if we are not
	 * 		currently translating the body of a function)
	 */
	public boolean isGlobalScope() {
		return mCurrentProcedureInfo == null;
	}

	/**
	 * @return the identifier of the current procedure whose scope we are currently in (i.e. we are currently
	 *  	translating the result's procedure body.
	 */
	public String getCurrentProcedureID() {
		if (mCurrentProcedureInfo == null) {
			throw new IllegalStateException("Check for isGlobalScope first");
		}
		return mCurrentProcedureInfo.getProcedureName();
//		if (mCurrentProcedure == null) {
//			return null;
//		}
//		return mCurrentProcedure.getIdentifier();
	}

//	public void addMemoryModelDeclarations(final MemoryModelDeclarations... mmdecls) {
//
//		final String currentProcId = mCurrentProcedure.getIdentifier();
//		Set<String> str = mCallGraphOld.get(currentProcId);
//		if (str == null) {
//			str = new LinkedHashSet<>();
//			mCallGraphOld.put(currentProcId, str);
//		}
//		for (final MemoryModelDeclarations mmdecl : mmdecls) {
//			str.add(mmdecl.getName());
//		}
//	}

//	public boolean noCurrentProcedure() {
//		return mCurrentProcedure == null;
//	}

//	public void addCallGraphEdge(final String source, final String target) {
//		Set<String> set = mCallGraphOld.get(source);
//		if (set == null) {
//			set = new LinkedHashSet<>();
//			mCallGraphOld.put(source, set);
//		}
//		set.add(target);
//	}

	public CFunction getCFunctionType(final String function) {
		final ProcedureInfo procInfo = this.getProcedureInfo(function);
		return procInfo.getCType();

//		return mProcedureToCFunctionType.get(function);
	}

	public Set<ProcedureSignature> getFunctionsSignaturesWithFunctionPointers() {
		return Collections.unmodifiableSet(mFunctionSignaturesThatHaveAFunctionPointer);
	}

	/**
	 *
	 * @param tentativeProcedureName
	 * @return true iff a procedure of the given name is known to the function handler
	 */
	public boolean hasProcedure(final String tentativeProcedureName) {
		return mProcedureNameToProcedureInfo.containsKey(tentativeProcedureName);
	}

	public void addModifiedGlobal(final String procedureName, final VariableLHS globalBoogieVarName) {
		getProcedureInfo(procedureName).addModifiedGlobal(globalBoogieVarName);
	}

	/**
	 * Adds a modified global for the procedure whose scope we are currently in.
	 *
	 * @param modifiedGlobal
	 */
	public void addModifiedGlobal(final VariableLHS modifiedGlobal) {
		if (mCurrentProcedureInfo == null) {
			throw new IllegalStateException();
		}
		mCurrentProcedureInfo.addModifiedGlobal(modifiedGlobal);

	}

	/**
	 * Contains information about a procedure in the target Boogie program.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 */
	static final class ProcedureInfo {

		/**
		 * the procedure's name (in the Boogie program)
		 */
		private final String mProcedureName;

		private CFunction mCType;

		private Procedure mDeclaration;
		private Procedure mImplementation;

		private final Set<VariableLHS> mModifiedGlobals;

		private boolean mModifiedGlobalsIsUsedDefined;


		ProcedureInfo(final String name) {
			mProcedureName = name;
			mModifiedGlobals = new LinkedHashSet<>();
		}

		public void resetCType(final CFunction cFunction) {
			assert mCType != null : "use setCType in this case";
			mCType = cFunction;
		}

		/**
		 * replace the existing declaration with another (refined) one
		 * @param procDecl
		 */
		public void resetDeclaration(final Procedure declaration) {
			assert declaration.getSpecification() != null;
			assert declaration.getBody() == null;
			mDeclaration = declaration;
		}

		public boolean hasDeclaration() {
			return mDeclaration != null;
		}

		public boolean hasImplementation() {
			return mImplementation != null;
		}

		public boolean hasCType() {
			return mCType != null;
		}

		public void addModifiedGlobals(final Set<VariableLHS> varNames) {
			mModifiedGlobals.addAll(varNames);
		}

		public void addModifiedGlobal(final VariableLHS varName) {
			mModifiedGlobals.add(varName);
		}

		public CFunction getCType() {
			if (mCType == null) {
				throw new IllegalStateException("query hasCType before calling this");
			}
			return mCType;
		}

		public void setCType(final CFunction cType) {
			assert mCType == null : "can only be set once!";
			mCType = cType;
		}

		/**
		 * Update the map procedureToCFunctionType according to the given arguments If a parameter is null, the
		 * corresponding value will not be changed. (for takesVarArgs, use "false" to change nothing).
		 */
		private void updateCFunction(final CType returnType,
				final CDeclaration[] allParamDecs,
				final CDeclaration oneParamDec, final boolean takesVarArgs) {
//			final CFunction oldCFunction = this.getCType();

//			final CType oldRetType = oldCFunction == null ? null : oldCFunction.getResultType();
			final CType oldRetType = this.hasCType() ? this.getCType().getResultType() : null;
			final CDeclaration[] oldInParams =
//					oldCFunction == null ? new CDeclaration[0] : oldCFunction.getParameterTypes();
					this.hasCType() ? this.getCType().getParameterTypes() : new CDeclaration[0];
//			final boolean oldTakesVarArgs = oldCFunction == null ? false : oldCFunction.takesVarArgs();
			final boolean oldTakesVarArgs = this.hasCType() ? this.getCType().takesVarArgs() : false;

			CType newRetType = oldRetType;
			CDeclaration[] newInParams = oldInParams;
			final boolean newTakesVarArgs = oldTakesVarArgs || takesVarArgs;

			if (allParamDecs != null) { // set a new parameter list
				assert oneParamDec == null;
				newInParams = allParamDecs;
			} else if (oneParamDec != null) { // add a parameter to the list
				assert allParamDecs == null;

				final ArrayList<CDeclaration> ips = new ArrayList<>(Arrays.asList(oldInParams));
				ips.add(oneParamDec);
				newInParams = ips.toArray(new CDeclaration[ips.size()]);
			}
			if (returnType != null) {
				newRetType = returnType;
			}

			if (this.hasCType()) {
				this.resetCType(new CFunction(newRetType, newInParams, newTakesVarArgs));
			} else {
				this.setCType(new CFunction(newRetType, newInParams, newTakesVarArgs));
			}
		}

		public Procedure getDeclaration() {
			if (mDeclaration == null) {
				throw new IllegalStateException("query hasDeclaration() first");
			}
			return mDeclaration;
		}

		public void setDeclaration(final Procedure declaration) {
			assert mDeclaration == null : "can only be set once!";
			assert declaration.getSpecification() != null;
			assert declaration.getBody() == null;
			mDeclaration = declaration;
		}

		public Procedure getImplementation() {
			return mImplementation;
		}

		public void setImplementation(final Procedure implementation) {
			assert mImplementation == null : "can only be set once!";
			assert implementation.getSpecification() == null;
			assert implementation.getBody() != null;
			mImplementation = implementation;
		}

		public boolean isModifiedGlobalsIsUsedDefined() {
			return mModifiedGlobalsIsUsedDefined;
		}

		public void setModifiedGlobalsIsUsedDefined(final boolean modifiedGlobalsIsUsedDefined) {
			mModifiedGlobalsIsUsedDefined = modifiedGlobalsIsUsedDefined;
		}

		public String getProcedureName() {
			return mProcedureName;
		}

		public Set<VariableLHS> getModifiedGlobals() {
			return Collections.unmodifiableSet(mModifiedGlobals);
		}

		@Override
		public String toString() {
			return mProcedureName + " : " + mCType;
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class ASTTypeComparisonVisitor extends GeneratedBoogieAstVisitor {

		private ASTType mOther;
		private boolean mResult;
		private boolean mIsFinished;

		public boolean isSimilar(final ASTType one, final ASTType other) {
			if (!isNonNull(one, other)) {
				return compareNull(one, other);
			}
			mOther = other;
			mIsFinished = false;
			mResult = true;
			one.accept(this);
			return mResult;
		}

		public boolean isSimilar(final VarList one, final VarList other) {
			if (!isNonNull(one, other)) {
				return compareNull(one, other);
			}

			if (one.getWhereClause() != null || other.getWhereClause() != null) {
				throw new UnsupportedOperationException("Not yet implemented: isSimilar for where clauses");
			}
			return isSimilar(one.getType(), other.getType());
		}

		@Override
		public boolean visit(final ArrayType node) {
			if (mIsFinished) {
				return false;
			}
			if (!(mOther instanceof ArrayType)) {
				return finishFalse();
			}

			final ArrayType other = (ArrayType) mOther;
			final ASTType[] oneIdxTypes = node.getIndexTypes();
			final ASTType[] otherIdxTypes = other.getIndexTypes();
			final ASTType oneValueType = node.getValueType();
			final ASTType otherValueType = other.getValueType();

			// check null
			if (!isNonNull(oneIdxTypes, otherIdxTypes)) {
				if (isNonNull(oneValueType, otherValueType)) {
					updateResult(compareNull(oneIdxTypes, otherIdxTypes) && compareNull(oneValueType, otherValueType));
				} else {
					updateResult(false);
				}
				mIsFinished = true;
				return false;
			}

			// check index types
			if (visit(oneIdxTypes, otherIdxTypes)) {
				mOther = otherValueType;
				oneValueType.accept(this);
				if (mIsFinished) {
					return false;
				}
			}

			mOther = other;
			return false;
		}

		@Override
		public boolean visit(final NamedType node) {
			if (mIsFinished) {
				return false;
			}
			if (!(mOther instanceof NamedType)) {
				return finishFalse();
			}
			final NamedType other = (NamedType) mOther;
			if (!Objects.equals(node.getName(), other.getName())) {
				return finishFalse();
			}

			final ASTType[] oneArgs = node.getTypeArgs();
			final ASTType[] otherArgs = other.getTypeArgs();
			visit(oneArgs, otherArgs);
			return false;
		}

		@Override
		public boolean visit(final PrimitiveType node) {
			if (mIsFinished) {
				return false;
			}
			if (!(mOther instanceof PrimitiveType)) {
				return finishFalse();
			}
			final PrimitiveType other = (PrimitiveType) mOther;
			updateResult(Objects.equals(node.getName(), other.getName()));
			return false;
		}

		@Override
		public boolean visit(final StructType node) {
			if (mIsFinished) {
				return false;
			}
			if (!(mOther instanceof StructType)) {
				return finishFalse();
			}

			final StructType other = (StructType) mOther;

			final VarList[] oneFields = node.getFields();
			final VarList[] otherFields = other.getFields();

			// check null
			if (!isNonNull(oneFields, otherFields)) {
				updateResult(compareNull(oneFields, otherFields));
				mIsFinished = true;
				return false;
			}

			if (oneFields.length != otherFields.length) {
				return finishFalse();
			}

			for (int i = 0; i < oneFields.length; ++i) {
				final VarList oneField = oneFields[i];
				final VarList otherField = otherFields[i];

				if (oneField.getWhereClause() != null || otherField.getWhereClause() != null) {
					throw new UnsupportedOperationException("Not yet implemented: where-clauses for struct nodes");
				}

				if (!isNonNull(oneField, otherField)) {
					if (compareNull(oneField, otherField)) {
						continue;
					}
					return finishFalse();
				}

				final ASTType oneType = oneField.getType();
				final ASTType otherType = otherField.getType();
				if (!isNonNull(oneType, otherType)) {
					if (compareNull(oneType, otherType)) {
						continue;
					}
					return finishFalse();
				}

				mOther = otherType;
				oneType.accept(this);
				if (mIsFinished) {
					return false;
				}
			}
			mOther = other;

			return false;
		}

		private boolean visit(final ASTType[] oneTypes, final ASTType[] otherTypes) {
			if (oneTypes.length != otherTypes.length) {
				return finishFalse();
			}
			final ASTType other = mOther;

			for (int i = 0; i < oneTypes.length; ++i) {
				final ASTType oneType = oneTypes[i];
				final ASTType otherType = otherTypes[i];
				if (!isNonNull(oneType, otherType)) {
					if (compareNull(oneType, otherType)) {
						continue;
					}
					return finishFalse();
				}

				mOther = otherType;
				oneType.accept(this);
				if (mIsFinished) {
					return false;
				}
			}
			mOther = other;
			return true;
		}

		private boolean finishFalse() {
			mResult = false;
			mIsFinished = true;
			return false;
		}

		private void updateResult(final boolean value) {
			mResult = mResult && value;
			if (mResult == false) {
				mIsFinished = true;
			}
		}

		private static boolean isNonNull(final Object one, final Object other) {
			return one != null && other != null;
		}

		private static boolean compareNull(final Object one, final Object other) {
			if (one == null && other == null) {
				return true;
			}
			if (one == null) {
				return false;
			}
			if (other == null) {
				return false;
			}
			throw new IllegalArgumentException("Both arguments are non-null");
		}
	}
}
