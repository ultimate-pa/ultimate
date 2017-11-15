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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Queue;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PRDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatSupportInUltimate;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CompoundStatementExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TarjanSCC;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.TranslationMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;

/**
 * Class that handles translation of functions.
 *
 * @author Markus Lindenmann
 * @date 12.10.2012
 * @author Alexander Nutz
 */
public class FunctionHandler {
	private static final String MSG_ONLY_ONE_ARG = " takes (exactly) one argument";

	/**
	 * A map from procedure name to procedure declaration.
	 */
	private final Map<String, Procedure> mProcedures;
	/**
	 * The currently handled procedure.
	 */
	private Procedure mCurrentProcedure;
	/**
	 * Whether the modified globals is user defined or not. If it is in this set, then it is a modifies clause defined
	 * by the user.
	 */
	private final Set<String> mModifiedGlobalsIsUserDefined;
	/**
	 * A map from method name to all called methods of the specified one.
	 */
	private final Map<String, Set<String>> mCallGraph;
	// /**
	// * Whether the current procedure is declared to return void.
	// */
	// private boolean mCurrentProcedureIsVoid;
	/**
	 * Modified global variables of the current function.
	 */
	private final Map<String, LinkedHashSet<String>> mModifiedGlobals;
	/**
	 * Methods that have been called before they were declared. These methods need a special treatment, as they are
	 * assumed to be returning int!
	 */
	private final Set<String> mMethodsCalledBeforeDeclared;

	private final Map<String, CFunction> mProcedureToCFunctionType;

	/**
	 * Herein the function Signatures (as a CFunction) are stored for which a boogie procedure has to be created in the
	 * postProcessor that deals with the function pointer calls that can happen.
	 */
	private final LinkedHashSet<ProcedureSignature> mFunctionSignaturesThatHaveAFunctionPointer;

	private final AExpressionTranslation mExpressionTranslation;
	private final TypeSizeAndOffsetComputer mTypeSizeComputer;

	/**
	 * Constructor.
	 *
	 * @param expressionTranslation
	 * @param typeSizeComputer
	 * @param checkMemoryLeakAtEndOfMain
	 */
	public FunctionHandler(final AExpressionTranslation expressionTranslation,
			final TypeSizeAndOffsetComputer typeSizeComputer) {
		mExpressionTranslation = expressionTranslation;
		mTypeSizeComputer = typeSizeComputer;
		mCallGraph = new LinkedHashMap<>();
		// mCurrentProcedureIsVoid = false;
		mModifiedGlobals = new LinkedHashMap<>();
		mMethodsCalledBeforeDeclared = new LinkedHashSet<>();
		mProcedures = new LinkedHashMap<>();
		mProcedureToCFunctionType = new LinkedHashMap<>();
		mModifiedGlobalsIsUserDefined = new LinkedHashSet<>();
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

		addAProcedure(main, loc, contract, methodName, funcType);

		return new SkipResult();
	}

	/**
	 * Handles translation of IASTFunctionDefinition.
	 *
	 * Note that a C function definition may have an ACSL specification while a Boogie procedure implementation does not
	 * have a specification (right?). Therefore we have to add any ACSL specs to the procedures member where the
	 * (Boogie) function declarations are stored.
	 *
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
		main.mCHandler.beginScope();

		final ILocation loc = main.getLocationFactory().createCLocation(node);
		final String methodName = cDec.getName();
		final CType returnCType = ((CFunction) cDec.getType()).getResultType();
		final boolean returnTypeIsVoid =
				returnCType instanceof CPrimitive && ((CPrimitive) returnCType).getType() == CPrimitives.VOID;

		updateCFunction(methodName, returnCType, null, null, false);

		VarList[] in = processInParams(main, loc, (CFunction) cDec.getType(), methodName);

		// There is only one return parameter in C, so this array always has size 1.
		VarList[] out = new VarList[1];
		final ASTType type = main.mTypeHandler.cType2AstType(loc, returnCType);

		if (returnTypeIsVoid) {
			// void, so there are no out vars
			out = new VarList[0];
		} else if (mMethodsCalledBeforeDeclared.contains(methodName)) {
			// defaulting to int, when a method is called that is only declared later
			final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);
			out[0] = new VarList(loc, new String[] { SFO.RES }, main.mTypeHandler.cType2AstType(loc, cPrimitive));
		} else {
			// "normal case"
			assert type != null;
			out[0] = new VarList(loc, new String[] { SFO.RES }, type);
		}
		Specification[] spec = makeBoogieSpecFromACSLContract(main, contract, methodName);

		Procedure proc = mProcedures.get(methodName);
		if (proc == null) {
			final Attribute[] attr = new Attribute[0];
			final String[] typeParams = new String[0];
			if (isInParamVoid(in)) {
				// in parameter is "void"
				in = new VarList[0];
			}
			proc = new Procedure(loc, attr, methodName, typeParams, in, out, spec, null);
			if (mProcedures.containsKey(methodName)) {
				final String msg =
						"Duplicated method identifier: " + methodName + ". C does not support function overloading!";
				throw new IncorrectSyntaxException(loc, msg);
			}
			mProcedures.put(methodName, proc);
		} else {
			// check declaration against its implementation
			VarList[] declIn = proc.getInParams();
			boolean checkInParams = true;
			if (in.length != proc.getInParams().length || out.length != proc.getOutParams().length
					|| isInParamVoid(proc.getInParams())) {
				if (proc.getInParams().length == 0) {
					// the implementation can have 0 to n in parameters!
					// do not check, but use the in params of the implementation
					// as we will take the ones of the implementation anyway
					checkInParams = false;
					declIn = in;
				} else if (isInParamVoid(proc.getInParams()) && (in.length == 0 || isInParamVoid(in))) {
					declIn = new VarList[0];
					in = new VarList[0];
					checkInParams = false;
				} else {
					final String msg = "Implementation does not match declaration!";
					throw new IncorrectSyntaxException(loc, msg);
				}
			}

			if (checkInParams) {
				final ASTTypeComparisonVisitor comparer = new ASTTypeComparisonVisitor();

				for (int i = 0; i < in.length; i++) {
					final boolean isSimilar = comparer.isSimilar(in[i], proc.getInParams()[i]);
					if (!isSimilar) {
						final String msg = "Implementation does not match declaration! "
								+ "Type missmatch on in-parameters! " + in.length + " arguments, "
								+ proc.getInParams().length + " parameters, " + "first missmatch at position " + i
								+ ", " + "argument type " + BoogiePrettyPrinter.print(in[i].getType()) + ", param type "
								+ BoogiePrettyPrinter.print(proc.getInParams()[i]);
						throw new IncorrectSyntaxException(loc, msg);
					}
				}
			}

			// combine the specification from the definition with the one from
			// the declaration
			final List<Specification> specFromDec = Arrays.asList(proc.getSpecification());
			final ArrayList<Specification> newSpecs = new ArrayList<>(Arrays.asList(spec));
			newSpecs.addAll(specFromDec);
			spec = newSpecs.toArray(new Specification[newSpecs.size()]);

			proc = new Procedure(proc.getLocation(), proc.getAttributes(), proc.getIdentifier(), proc.getTypeParams(),
					declIn, proc.getOutParams(), spec, null);
			mProcedures.put(methodName, proc);
		}
		final Procedure declWithCorrectlyNamedInParams = new Procedure(proc.getLocation(), proc.getAttributes(),
				proc.getIdentifier(), proc.getTypeParams(), in, proc.getOutParams(), proc.getSpecification(), null);
		mCurrentProcedure = declWithCorrectlyNamedInParams;
		// mCurrentProcedureIsVoid = returnTypeIsVoid;
		final String procId = mCurrentProcedure.getIdentifier();

		addModifiedGlobalEntry(procId);
		addCallGraphNode(procId);

		/*
		 * The structure is as follows: 1) Preprocessing of the method body: - add new variables for parameters - havoc
		 * them - etc. 2) dispatch body 3) handle mallocs 4) add statements and declarations to new body
		 */
		ArrayList<Statement> stmts = new ArrayList<>();
		final ArrayList<Declaration> decls = new ArrayList<>();
		// 1)
		handleFunctionsInParams(main, loc, memoryHandler, decls, stmts, node);
		// 2)
		// Body body = ((Body) main.dispatch(node.getBody()).node);
		// stmts.addAll(Arrays.asList(body.getBlock()));
		// for (VariableDeclaration declaration : body.getLocalVars()) {
		// decls.add(declaration);
		// }
		final CompoundStatementExpressionResult cser =
				(CompoundStatementExpressionResult) main.dispatch(node.getBody());
		stmts.addAll(cser.stmt);
		decls.addAll(cser.decl);

		// 3) ,4)
		stmts = ((CHandler) main.mCHandler).updateStmtsAndDeclsAtScopeEnd(main, decls, stmts);

		final Body body = new Body(loc, decls.toArray(new VariableDeclaration[decls.size()]),
				stmts.toArray(new Statement[stmts.size()]));

		proc = mCurrentProcedure;
		// Implementation -> Specification always null!
		final Procedure impl = new Procedure(loc, proc.getAttributes(), methodName, proc.getTypeParams(), in,
				proc.getOutParams(), null, body);
		mCurrentProcedure = null;
		// mCurrentProcedureIsVoid = false;
		main.mCHandler.endScope();
		return new Result(impl);
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
		final VarList[] outParams = mCurrentProcedure.getOutParams();
		final ExpressionResult rExp = new ExpressionResult(stmt, null, decl, auxVars, overApp);
		// if (mMethodsCalledBeforeDeclared.contains(mCurrentProcedure.getIdentifier()) && mCurrentProcedureIsVoid) {
		if (mMethodsCalledBeforeDeclared.contains(mCurrentProcedure.getIdentifier())
				&& mCurrentProcedure.getOutParams().length == 0) {
			// void method that was assumed to be returning int! -> return int
			final String id = outParams[0].getIdentifiers()[0];
			final VariableLHS lhs = new VariableLHS(loc, id);
			final Statement havoc = new HavocStatement(loc, new VariableLHS[] { lhs });
			stmt.add(havoc);
		} else if (node.getReturnValue() != null) {
			final ExpressionResult exprResult = ((ExpressionResult) main.dispatch(node.getReturnValue()))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			exprResult.rexBoolToIntIfNecessary(loc, mExpressionTranslation);

			// do some implicit casts
			final CType functionResultType =
					mProcedureToCFunctionType.get(mCurrentProcedure.getIdentifier()).getResultType();
			if (!exprResult.lrVal.getCType().equals(functionResultType) && functionResultType instanceof CPointer
					&& exprResult.lrVal.getCType() instanceof CPrimitive
					&& exprResult.lrVal.getValue() instanceof IntegerLiteral
					&& "0".equals(((IntegerLiteral) exprResult.lrVal.getValue()).getValue())) {
				exprResult.lrVal = new RValue(mExpressionTranslation.constructNullPointer(loc), functionResultType);
			}

			stmt.addAll(exprResult.stmt);
			decl.addAll(exprResult.decl);
			auxVars.putAll(exprResult.auxVars);
			overApp.addAll(exprResult.overappr);
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
				rExp.lrVal = exprResult.lrVal;
				main.mCHandler.convert(loc, rExp, functionResultType);
				final RValue castExprResultRVal = (RValue) rExp.lrVal;
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
	 * Calculates transitive modifies clauses for all procedure declarations linear in time to (|procedures| +
	 * |procedure calls|).
	 *
	 * addition (alex, may 2014): for every modifies clause: if one memory-array is included, all active memory arrays
	 * have to be included (f.i. we have procedure modifies memory_int, and memoryHandler.isFloatMMArray == true, and
	 * memoryHandler.isIntMMArray == true, memoryHandler.isPointerMMArray == false, then we have to add memory_real to
	 * the modifies clause of procedure
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @return procedure declarations
	 */
	public List<Declaration> calculateTransitiveModifiesClause(final Dispatcher main,
			final MemoryHandler memoryHandler) {
		final String notDeclaredProcedureName = isEveryCalledProcedureDeclared();
		if (notDeclaredProcedureName != null) {
			throw new UndeclaredFunctionException(null, "a function that is called in the program "
					+ "is not declared in the program: " + notDeclaredProcedureName);
		}
		// calculate SCCs and a mapping for each methodId to its SCC
		// O(|edges| + |calls|)
		final Set<Set<String>> sccs = new TarjanSCC().getSCCs(mCallGraph);
		final Map<String, Set<String>> functionNameToScc = new LinkedHashMap<>();
		for (final Set<String> scc : sccs) { // O(|proc|)
			for (final String s : scc) {
				functionNameToScc.put(s, scc);
			}
		}
		// counts how many incoming edges an scc has in the updateGraph
		final Map<Set<String>, Integer> incomingEdges = new LinkedHashMap<>();
		for (final Set<String> scc : sccs) {
			incomingEdges.put(scc, 0);
		}
		// calculate the SCC update graph without loops and dead ends
		final Queue<Set<String>> deadEnds = new LinkedList<>();
		deadEnds.addAll(sccs);

		// updateGraph maps a calleeSCC to many callerSCCs
		// This graph might not be complete! It is i.e. missing all procedures,
		// that do not have incoming or outgoing edges!
		// But: They don't need an update anyway!
		final Map<Set<String>, Set<Set<String>>> updateGraph = new LinkedHashMap<>();
		for (final Entry<String, Set<String>> entry : mCallGraph.entrySet()) {
			final String caller = entry.getKey();
			// O(|calls|)
			for (final String callee : entry.getValue()) {
				// foreach s : succ(p)
				final Set<String> sccCaller = functionNameToScc.get(caller);
				final Set<String> sccCallee = functionNameToScc.get(callee);
				if (sccCaller == sccCallee) {
					// skip self loops
					continue;
				}
				if (updateGraph.containsKey(sccCallee)) {
					updateGraph.get(sccCallee).add(sccCaller);
				} else {
					final Set<Set<String>> predSCCs = new LinkedHashSet<>();
					predSCCs.add(sccCaller);
					updateGraph.put(sccCallee, predSCCs);
				}
				deadEnds.remove(sccCaller);
			}
		}

		// incoming edges must be computed on a graph that has Sccs as nodes (updategraph), not just the functions
		// (callgraph)
		for (final Entry<Set<String>, Set<Set<String>>> entry : updateGraph.entrySet()) {
			for (final Set<String> callerScc : entry.getValue()) {
				incomingEdges.put(callerScc, incomingEdges.get(callerScc) + 1);
			}
		}

		// calculate transitive modifies clause
		final Map<Set<String>, Set<String>> sccToModifiedGlobals = new LinkedHashMap<>();
		while (!deadEnds.isEmpty()) {
			// O (|proc| + |edges in updateGraph|), where
			// |edges in updateGraph| <= |calls|
			final Set<String> deadEnd = deadEnds.poll();

			// the modified globals of the scc is the union of the modified globals of all its functions
			for (final String func : deadEnd) {
				if (!sccToModifiedGlobals.containsKey(deadEnd)) {
					sccToModifiedGlobals.put(deadEnd, new LinkedHashSet<>(mModifiedGlobals.get(func)));
				} else {
					sccToModifiedGlobals.get(deadEnd).addAll(mModifiedGlobals.get(func));
				}
			}

			// if the scc has no callers, do nothing with it
			if (updateGraph.get(deadEnd) == null) {
				continue;
			}

			// for all callers of the scc, add the modified globals to them, make them deadends, if all their input has
			// been processed
			for (final Set<String> caller : updateGraph.get(deadEnd)) {
				if (!sccToModifiedGlobals.containsKey(caller)) {
					final Set<String> n = new LinkedHashSet<>();
					n.addAll(sccToModifiedGlobals.get(deadEnd));
					sccToModifiedGlobals.put(caller, n);
				} else {
					sccToModifiedGlobals.get(caller).addAll(sccToModifiedGlobals.get(deadEnd));
				}
				final int remainingUpdates = incomingEdges.get(caller) - 1;
				if (remainingUpdates == 0) {
					deadEnds.add(caller);
				}
				incomingEdges.put(caller, remainingUpdates);
			}
		}
		// update the modifies clauses!
		final ArrayList<Declaration> declarations = new ArrayList<>();
		for (final Procedure procDecl : mProcedures.values()) { // O(|proc|)
			final String mId = procDecl.getIdentifier();
			Specification[] spec = procDecl.getSpecification();
			final CACSLLocation loc = (CACSLLocation) procDecl.getLocation();
			if (!mModifiedGlobalsIsUserDefined.contains(mId)) {
				assert functionNameToScc.get(mId) != null;
				final Set<String> currModClause = sccToModifiedGlobals.get(functionNameToScc.get(mId));
				assert currModClause != null : "No modifies clause proc " + mId;

				mModifiedGlobals.get(mId).addAll(currModClause);
				final int nrSpec = spec.length;
				spec = Arrays.copyOf(spec, nrSpec + 1);
				final LinkedHashSet<String> modifySet = new LinkedHashSet<>();

				for (final String var : mModifiedGlobals.get(mId)) {
					modifySet.add(var);
				}

				{
					/*
					 * add missing heap arrays If the procedure modifies one heap array, we add all heap arrays. This is
					 * a workaround. We cannot add all procedures immediately, because we do not know all heap arrays in
					 * advance since they are added lazily on demand.
					 *
					 */
					final Collection<HeapDataArray> heapDataArrays = memoryHandler.getMemoryModel()
							.getDataHeapArrays(memoryHandler.getRequiredMemoryModelFeatures());
					if (containsOneHeapDataArray(modifySet, heapDataArrays)) {
						for (final HeapDataArray hda : heapDataArrays) {
							modifySet.add(hda.getVariableName());
						}
					}
				}

				final VariableLHS[] modifyList = new VariableLHS[modifySet.size()];
				{
					int i = 0;
					for (final String modifyEntry : modifySet) {
						modifyList[i++] = new VariableLHS(loc, modifyEntry);
					}
				}
				spec[nrSpec] = new ModifiesSpecification(loc, false, modifyList);
			}
			final String lol = main.getCheckedMethod();
			if (memoryHandler.getRequiredMemoryModelFeatures().isMemoryModelInfrastructureRequired() && (main
					.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_ALLOCATION_PURITY)
					|| (main.getCheckedMethod().equals(SFO.EMPTY) || main.getCheckedMethod().equals(mId)) && main
							.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_MEMORY_LEAK_IN_MAIN))) {
				// add a specification to check for memory leaks
				final Expression vIe = new IdentifierExpression(loc, SFO.VALID);
				final int nrSpec = spec.length;
				final Check check = new Check(Check.Spec.MEMORY_LEAK);
				final ILocation ensLoc = LocationFactory.createLocation(loc, check);
				spec = Arrays.copyOf(spec, nrSpec + 1);
				spec[nrSpec] = new EnsuresSpecification(ensLoc, false,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, vIe,
								ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.OLD, vIe)));
				check.annotate(spec[nrSpec]);
				if (main.getPreferences()
						.getBoolean(CACSLPreferenceInitializer.LABEL_SVCOMP_MEMTRACK_COMPATIBILITY_MODE)) {
					new Overapprox(Collections.singletonMap("memtrack", ensLoc)).annotate(spec[nrSpec]);
				}
			}
			declarations.add(new Procedure(loc, procDecl.getAttributes(), mId, procDecl.getTypeParams(),
					procDecl.getInParams(), procDecl.getOutParams(), spec, null));
		}
		return declarations;
	}

	private static boolean containsOneHeapDataArray(final LinkedHashSet<String> modifySet,
			final Collection<HeapDataArray> heapDataArrays) {
		for (final HeapDataArray hda : heapDataArrays) {
			if (modifySet.contains(hda.getVariableName())) {
				return true;
			}
		}
		return false;
	}

	private Result handleFunctionCallGivenNameAndArguments(final Dispatcher main, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final ILocation loc, final String methodName,
			final IASTInitializerClause[] arguments) {

		mCallGraph.get(mCurrentProcedure.getIdentifier()).add(methodName);

		final boolean procedureDeclaredWithOutInparamsButCalledWithInParams =
				mProcedures.get(methodName) != null && mProcedures.get(methodName).getBody() == null
						&& mProcedures.get(methodName).getInParams().length == 0;

		// if the function has varArgs, we throw away all parameters that belong
		// to the varArgs part and only keep the normal ones
		IASTInitializerClause[] inParams = arguments;
		if (mProcedureToCFunctionType.containsKey(methodName)
				&& mProcedureToCFunctionType.get(methodName).takesVarArgs()) {
			final int noParameterWOVarArgs = mProcedureToCFunctionType.get(methodName).getParameterTypes().length;
			inParams = new IASTInitializerClause[noParameterWOVarArgs];
			System.arraycopy(arguments, 0, inParams, 0, noParameterWOVarArgs);
			// .. and if it is really called with more that its normal parameter
			// number, we throw an exception, because we may be unsound
			// (the code before this does not make that much sense, but maybe some
			// day we want that solution again..
			if (!main.getPreferences().getEnum(CACSLPreferenceInitializer.LABEL_MODE, TranslationMode.class)
					.equals(TranslationMode.SV_COMP14) && inParams.length < arguments.length) {
				throw new UnsupportedSyntaxException(loc, "we cannot deal with varargs right now");
			}
		}

		if (mProcedures.containsKey(methodName) && inParams.length != mProcedures.get(methodName).getInParams().length
				&& !(mProcedures.get(methodName).getInParams().length == 1
						&& mProcedures.get(methodName).getInParams()[0].getType() == null && inParams.length == 0)
				&& !procedureDeclaredWithOutInparamsButCalledWithInParams) {
			// ok, if the procedure is declared (and not implemented) as having no parameters --> then we may call it
			// with parameters later
			final String msg = "Function call has incorrect number of in-params!";
			throw new IncorrectSyntaxException(loc, msg);
		}
		// this means param of declaration is void and parameter
		// list of call is empty! --> OK

		// dispatch the inparams
		final ArrayList<Expression> args = new ArrayList<>();
		final ArrayList<Statement> stmt = new ArrayList<>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ArrayList<Overapprox> overappr = new ArrayList<>();
		for (int i = 0; i < inParams.length; i++) {
			final IASTInitializerClause inParam = inParams[i];
			ExpressionResult in = (ExpressionResult) main.dispatch(inParam);

			if (in.lrVal.getCType().getUnderlyingType() instanceof CArray) {
				// arrays are passed as pointers --> switch to RValue would make a boogie array..
				final CType valueType =
						((CArray) in.lrVal.getCType().getUnderlyingType()).getValueType().getUnderlyingType();
				if (in.lrVal instanceof HeapLValue) {
					in.lrVal = new RValue(((HeapLValue) in.lrVal).getAddress(), new CPointer(valueType));
				} else {
					in.lrVal = new RValue(in.lrVal.getValue(), new CPointer(valueType));
				}
			} else {
				in = in.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			}

			if (in.lrVal.getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}

			// if the procedure is declared (and not implemented) as having no
			// parameters --> then we may call it with parameters later
			// --> but from then on we know its parameters
			if (procedureDeclaredWithOutInparamsButCalledWithInParams) {
				// add the current parameter to the procedure's signature
				updateCFunction(methodName, null, null, new CDeclaration(in.lrVal.getCType(), SFO.IN_PARAM + i), false);
			} else if (mProcedureToCFunctionType.containsKey(methodName)) {
				// we already know the parameters: do implicit casts and bool/int conversion
				CType expectedParamType =
						mProcedureToCFunctionType.get(methodName).getParameterTypes()[i].getType().getUnderlyingType();
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
			args.add(in.lrVal.getValue());
			stmt.addAll(in.stmt);
			decl.addAll(in.decl);
			auxVars.putAll(in.auxVars);
			overappr.addAll(in.overappr);
		}

		if (procedureDeclaredWithOutInparamsButCalledWithInParams) {
			final VarList[] procParams =
					new VarList[mProcedureToCFunctionType.get(methodName).getParameterTypes().length];
			for (int i = 0; i < procParams.length; i++) {
				procParams[i] = new VarList(loc,
						new String[] { mProcedureToCFunctionType.get(methodName).getParameterTypes()[i].getName() },
						((TypeHandler) main.mTypeHandler).cType2AstType(loc,
								mProcedureToCFunctionType.get(methodName).getParameterTypes()[i].getType()));
			}
			final Procedure currentProc = mProcedures.get(methodName);
			final Procedure newProc = new Procedure(currentProc.getLocation(), currentProc.getAttributes(),
					currentProc.getIdentifier(), currentProc.getTypeParams(), procParams, currentProc.getOutParams(),
					currentProc.getSpecification(), currentProc.getBody());
			mProcedures.put(methodName, newProc);
		}

		return makeTheFunctionCallItself(main, loc, methodName, stmt, decl, auxVars, overappr, args);
	}

	/**
	 * Checks if the methodname is a function where we have our own specification or implementation and returns that in
	 * case. (This is typically the case for functions defined in the C standard.)
	 *
	 * @param main
	 * @param memoryHandler
	 * @param structHandler
	 * @param loc
	 * @param methodName
	 * @param arguments
	 * @return
	 */
	public Result handleStandardFunctions(final Dispatcher main, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final AExpressionTranslation expressionTranslation, final ILocation loc,
			final String methodName, final IASTInitializerClause[] arguments) {
		if ("malloc".equals(methodName) || "alloca".equals(methodName) || "__builtin_alloca".equals(methodName)) {
			assert arguments.length == 1;
			ExpressionResult exprRes = (ExpressionResult) main.dispatch(arguments[0]);
			exprRes = exprRes.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			main.mCHandler.convert(loc, exprRes, mTypeSizeComputer.getSizeT());

			final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
			final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MALLOC, resultType);
			final VariableDeclaration tmpVarDecl =
					SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.constructPointerType(loc), loc);
			exprRes.decl.add(tmpVarDecl);

			exprRes.stmt.add(memoryHandler.getMallocCall(exprRes.lrVal.getValue(), tmpId, loc));
			exprRes.lrVal = new RValue(new IdentifierExpression(loc, tmpId), resultType);

			// for alloc a we have to free the variable ourselves when the
			// stackframe is closed, i.e. at a return
			if ("alloca".equals(methodName) || "__builtin_alloca".equals(methodName)) {
				final LocalLValue llVal = new LocalLValue(new VariableLHS(loc, tmpId), resultType);
				memoryHandler.addVariableToBeFreed(main,
						new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
				// we need to clear auxVars because otherwise the malloc auxvar is havocced after
				// this, and free (triggered by the statement before) would fail.
				exprRes.auxVars.clear();
			}
			return exprRes;
		} else if ("free".equals(methodName)) {
			assert arguments.length == 1;
			final Result pRes = main.dispatch(arguments[0]);
			assert pRes instanceof ExpressionResult;
			final ExpressionResult pRex =
					((ExpressionResult) pRes).switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			pRex.stmt.add(memoryHandler.getFreeCall(main, this, pRex.lrVal, loc));
			return pRex;
		} else if ("calloc".equals(methodName)) {
			/*
			 * C11 says in 7.22.3.2 void *calloc(size_t nmemb, size_t size); The calloc function allocates space for an
			 * array of nmemb objects, each of whose size is size. The space is initialized to all bits zero.
			 */
			assert arguments.length == 2;
			final ExpressionResult nmemb = ((ExpressionResult) main.dispatch(arguments[0]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			main.mCHandler.convert(loc, nmemb, mTypeSizeComputer.getSizeT());
			final ExpressionResult size = ((ExpressionResult) main.dispatch(arguments[1]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			main.mCHandler.convert(loc, size, mTypeSizeComputer.getSizeT());

			final Expression product = mExpressionTranslation.constructArithmeticExpression(loc,
					IASTBinaryExpression.op_multiply, nmemb.lrVal.getValue(), mTypeSizeComputer.getSizeT(),
					size.lrVal.getValue(), mTypeSizeComputer.getSizeT());
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(nmemb, size);

			final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
			final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MALLOC, resultType);
			final VariableDeclaration tmpVarDecl =
					SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.constructPointerType(loc), loc);
			result.decl.add(tmpVarDecl);

			result.stmt.add(memoryHandler.getMallocCall(product, tmpId, loc));
			result.lrVal = new RValue(new IdentifierExpression(loc, tmpId), resultType);

			result.stmt.add(memoryHandler.constructUltimateMeminitCall(loc, nmemb.lrVal.getValue(),
					size.lrVal.getValue(), product, new IdentifierExpression(loc, tmpId)));

			if (mCallGraph.get(mCurrentProcedure.getIdentifier()) == null) {
				mCallGraph.put(mCurrentProcedure.getIdentifier(), new LinkedHashSet<String>());
			}
			mCallGraph.get(mCurrentProcedure.getIdentifier()).add(MemoryModelDeclarations.Ultimate_MemInit.getName());
			mCallGraph.get(mCurrentProcedure.getIdentifier()).add(MemoryModelDeclarations.Ultimate_Alloc.getName());

			return result;
		} else if ("memset".equals(methodName)) {
			/*
			 * C11 says in 7.24.6.1 void *memset(void *s, int c, size_t n); The memset function copies the value of c
			 * (converted to an unsigned char) into each of the first n characters of the object pointed to by s.
			 */
			assert arguments.length == 3 : "wrong number of arguments";
			final ExpressionResult argS = ((ExpressionResult) main.dispatch(arguments[0]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			final ExpressionResult argC = ((ExpressionResult) main.dispatch(arguments[1]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			mExpressionTranslation.convertIntToInt(loc, argC, new CPrimitive(CPrimitives.INT));
			final ExpressionResult argN = ((ExpressionResult) main.dispatch(arguments[2]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			mExpressionTranslation.convertIntToInt(loc, argN, mTypeSizeComputer.getSizeT());

			final ExpressionResult result = new ExpressionResult(argS.lrVal);
			result.addAll(argS);
			result.addAll(argC);
			result.addAll(argN);

			final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MEMSETRES,
					new CPointer(new CPrimitive(CPrimitives.VOID)));
			final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] {
					new VarList(loc, new String[] { tId }, main.mTypeHandler.constructPointerType(loc)) });
			result.decl.add(tVarDecl);
			result.auxVars.put(tVarDecl, loc);

			result.stmt.add(memoryHandler.constructUltimateMemsetCall(loc, argS.lrVal.getValue(), argC.lrVal.getValue(),
					argN.lrVal.getValue(), tId));

			if (mCallGraph.get(mCurrentProcedure.getIdentifier()) == null) {
				mCallGraph.put(mCurrentProcedure.getIdentifier(), new LinkedHashSet<String>());
			}
			mCallGraph.get(mCurrentProcedure.getIdentifier()).add(MemoryModelDeclarations.C_Memset.getName());

			return result;
			// } else if (methodName.equals("sqrt") ||
			// Arrays.asList(SFO.FLOAT_CLASSIFICATION_FUNCTION).contains(methodName)) {
			// assert arguments.length == 1;
			// final ExpressionResult arg = ((ExpressionResult) main.dispatch(arguments[0]))
			// .switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			// if (Arrays.asList(SFO.FLOAT_CLASSIFICATION_FUNCTION).contains(methodName)) {
			// final CPrimitive expectedType = BitvectorTranslation.getParamTypeForFpClassification(methodName);
			// if (expectedType != null) {
			// mExpressionTranslation.convertFloatToFloat(loc, arg, expectedType);
			// }
			// }
			// final RValue rvalue = mExpressionTranslation.constructOtherUnaryFloatOperation(loc, methodName, (RValue)
			// arg.lrVal);
			// final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(arg);
			// result.lrVal = rvalue;
			// return result;
		} else if ("__builtin_huge_val".equals(methodName)) {
			return mExpressionTranslation.createNanOrInfinity(loc, "inf");
		} else if ("__builtin_unreachable".equals(methodName)) {
			// TODO: Add option that allows us to check for builtin_unreachable by adding assert
			// return new ExpressionResult(Collections.singletonList(new AssertStatement(loc,
			// new de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral(loc, false))), null);
			// TODO: Add option that just ignores the function:
			// return new SkipResult();
			// TODO: Keep the following code, but add it as option together with the other two
			return new ExpressionResult(Collections.singletonList(new AssumeStatement(loc,
					new de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral(loc, false))), null);

		} else if ("__builtin_huge_valf".equals(methodName)) {
			return mExpressionTranslation.createNanOrInfinity(loc, "inff");
		} else if ("__builtin_strchr".equals(methodName) || "strchr".equals(methodName)) {
			/*
			 * C11, 7.21.5.2 says: "#include <string.h> char *strchr(const char *s, int c); Description: The strchr
			 * function locates the first occurrence of c (converted to a char) in the string pointed to by s. The
			 * terminating null character is considered to be part of the string. Returns : The strchr function returns
			 * a pointer to the located character, or a null pointer if the character does not occur in the string."
			 *
			 * We replace the method call by a fresh char pointer variable which is havocced, and assumed to be either
			 * NULL or a pointer into the area where the argument pointer is valid.
			 */
			final ExpressionResultBuilder builder = new ExpressionResultBuilder();

			// dispatch first argument -- we need its value for the assume
			assert arguments.length == 2 : "wrong number of arguments";
			final ExpressionResult argS = ((ExpressionResult) main.dispatch(arguments[0]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			builder.addDeclarations(argS.decl).addStatements(argS.stmt).addOverapprox(argS.overappr)
					.putAuxVars(argS.auxVars).addNeighbourUnionFields(argS.otherUnionFields);

			// dispatch second argument -- only for its sideeffects
			final ExpressionResult argC = ((ExpressionResult) main.dispatch(arguments[0]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			builder.addDeclarations(argC.decl).addStatements(argC.stmt).addOverapprox(argC.overappr)
					.putAuxVars(argC.auxVars).addNeighbourUnionFields(argC.otherUnionFields);

			// introduce fresh aux variable
			final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.CHAR));
			final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
			final VariableDeclaration tmpVarDecl =
					SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.constructPointerType(loc), loc);
			builder.addDeclaration(tmpVarDecl);
			builder.putAuxVar(tmpVarDecl, loc);

			final Expression nullExpr = expressionTranslation.constructNullPointer(loc);

			/*
			 * if we are in memsafety-mode: add assertions that check that arg_s.lrVal.getValue is a valid pointer
			 *
			 * technical Notes: these assertions are added before the assume statement and before the result can be
			 * assigned thus the overapproximation introduced does not affect violations of these assertions
			 */
			builder.addStatements(constructMemsafetyChecksForPointerExpression(loc, argS.lrVal.getValue(),
					memoryHandler, expressionTranslation));

			// the havocced/uninitialized variable that represents the return value
			final Expression tmpExpr = new IdentifierExpression(loc, tmpId);

			/*
			 * build the assume statement as described above
			 */
			{
				// res.base == 0 && res.offset == 0
				final Expression baseEqualsNull = expressionTranslation.constructBinaryComparisonIntegerExpression(loc,
						IASTBinaryExpression.op_equals, MemoryHandler.getPointerBaseAddress(tmpExpr, loc),
						expressionTranslation.getCTypeOfPointerComponents(),
						MemoryHandler.getPointerBaseAddress(nullExpr, loc),
						expressionTranslation.getCTypeOfPointerComponents());
				final Expression offsetEqualsNull = expressionTranslation.constructBinaryComparisonIntegerExpression(
						loc, IASTBinaryExpression.op_equals, MemoryHandler.getPointerOffset(tmpExpr, loc),
						expressionTranslation.getCTypeOfPointerComponents(),
						MemoryHandler.getPointerOffset(nullExpr, loc),
						expressionTranslation.getCTypeOfPointerComponents());
				final BinaryExpression equalsNull =
						new BinaryExpression(loc, Operator.LOGICAND, baseEqualsNull, offsetEqualsNull);
				// old solution did not work quickly..
				// final BinaryExpression equalsNull = expressionTranslation.constructBinaryComparisonExpression(loc,
				// new BinaryExpression(loc, Operator.COMPEQ, tmpExpr, nullExpr);
				// res.base == arg_s.base
				final Expression baseEquals = expressionTranslation.constructBinaryComparisonIntegerExpression(loc,
						IASTBinaryExpression.op_equals, MemoryHandler.getPointerBaseAddress(tmpExpr, loc),
						expressionTranslation.getCTypeOfPointerComponents(),
						MemoryHandler.getPointerBaseAddress(argS.lrVal.getValue(), loc),
						expressionTranslation.getCTypeOfPointerComponents());
				// res.offset >= 0
				final Expression offsetNonNegative = expressionTranslation.constructBinaryComparisonIntegerExpression(
						loc, IASTBinaryExpression.op_lessEqual,
						expressionTranslation.constructLiteralForIntegerType(loc,
								expressionTranslation.getCTypeOfPointerComponents(), new BigInteger("0")),
						expressionTranslation.getCTypeOfPointerComponents(),
						MemoryHandler.getPointerOffset(tmpExpr, loc),
						expressionTranslation.getCTypeOfPointerComponents());
				// res.offset < length(arg_s.base)
				final Expression offsetSmallerLength = expressionTranslation.constructBinaryComparisonIntegerExpression(
						loc, IASTBinaryExpression.op_lessEqual, MemoryHandler.getPointerOffset(tmpExpr, loc),
						expressionTranslation.getCTypeOfPointerComponents(),
						ExpressionFactory.constructNestedArrayAccessExpression(loc, memoryHandler.getLengthArray(loc),
								new Expression[] { MemoryHandler.getPointerBaseAddress(argS.lrVal.getValue(), loc) }),
						expressionTranslation.getCTypeOfPointerComponents());
				// res.base == arg_s.base && res.offset >= 0 && res.offset <= length(arg_s.base)
				final BinaryExpression inRange = new BinaryExpression(loc, Operator.LOGICAND, baseEquals,
						new BinaryExpression(loc, Operator.LOGICAND, offsetNonNegative, offsetSmallerLength));
				// assume equalsNull or inRange
				final AssumeStatement assume =
						new AssumeStatement(loc, new BinaryExpression(loc, Operator.LOGICOR, equalsNull, inRange));
				builder.addStatement(assume);
			}

			// final List<Overapprox> overapprox = new ArrayList<>();
			final Overapprox overappFlag = new Overapprox("builtin_strchr", loc);
			// overapprox.add(overappFlag);
			// assume.getPayload().getAnnotations().put(Overapprox.getIdentifier(), overappFlag);
			builder.addOverapprox(overappFlag);

			final RValue lrVal = new RValue(tmpExpr, resultType);
			builder.setLRVal(lrVal);

			return builder.build();
		} else if ("__builtin_strlen".equals(methodName) || "strlen".equals(methodName)) {
			if (arguments.length != 1) {
				throw new IllegalArgumentException("strlen has one argument");
			}
			final ExpressionResultBuilder builder = new ExpressionResultBuilder();

			final ExpressionResult arg = ((ExpressionResult) main.dispatch(arguments[0]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			builder.addDeclarations(arg.decl);
			builder.addStatements(arg.stmt);
			builder.addOverapprox(arg.overappr);
			builder.putAuxVars(arg.auxVars);
			builder.addNeighbourUnionFields(arg.otherUnionFields);

			builder.addStatements(constructMemsafetyChecksForPointerExpression(loc, arg.lrVal.getValue(), memoryHandler,
					expressionTranslation));

			// according to standard result is size_t, we use int for efficiency
			final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
			// introduce fresh aux variable
			final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
			final VariableDeclaration tmpVarDecl =
					SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.cType2AstType(loc, resultType), loc);
			builder.addDeclaration(tmpVarDecl);
			builder.putAuxVar(tmpVarDecl, loc);

			final IdentifierExpression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
			final Overapprox overAppFlag = new Overapprox(methodName, loc);
			builder.addOverapprox(overAppFlag);
			final RValue lrVal = new RValue(tmpVarIdExpr, resultType);
			builder.setLRVal(lrVal);
			return builder.build();

		} else if ("__builtin_strcmp".equals(methodName) || "strcmp".equals(methodName)) {
			if (arguments.length != 2) {
				throw new IllegalArgumentException("strcmp has two arguments");
			}
			final ExpressionResultBuilder builder = new ExpressionResultBuilder();

			final ExpressionResult arg0 = ((ExpressionResult) main.dispatch(arguments[0]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			builder.addDeclarations(arg0.decl);
			builder.addStatements(arg0.stmt);
			builder.addOverapprox(arg0.overappr);
			builder.putAuxVars(arg0.auxVars);
			builder.addNeighbourUnionFields(arg0.otherUnionFields);

			builder.addStatements(constructMemsafetyChecksForPointerExpression(loc, arg0.lrVal.getValue(),
					memoryHandler, expressionTranslation));

			final ExpressionResult arg1 = ((ExpressionResult) main.dispatch(arguments[1]))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			builder.addDeclarations(arg1.decl);
			builder.addStatements(arg1.stmt);
			builder.addOverapprox(arg1.overappr);
			builder.putAuxVars(arg1.auxVars);
			builder.addNeighbourUnionFields(arg1.otherUnionFields);

			builder.addStatements(constructMemsafetyChecksForPointerExpression(loc, arg1.lrVal.getValue(),
					memoryHandler, expressionTranslation));

			final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
			// introduce fresh aux variable
			final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
			final VariableDeclaration tmpVarDecl =
					SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.cType2AstType(loc, resultType), loc);
			builder.addDeclaration(tmpVarDecl);
			builder.putAuxVar(tmpVarDecl, loc);

			final IdentifierExpression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
			final Overapprox overAppFlag = new Overapprox(methodName, loc);
			builder.addOverapprox(overAppFlag);
			final RValue lrVal = new RValue(tmpVarIdExpr, resultType);
			builder.setLRVal(lrVal);
			return builder.build();
		} else if ("__builtin_return_address".equals(methodName)) {
			if (arguments.length != 1) {
				throw new IllegalArgumentException(methodName + MSG_ONLY_ONE_ARG);
			}
			main.dispatch(arguments[0]);
			/*
			 * The GNU C online documentation at https://gcc.gnu.org/onlinedocs/gcc/Return-Address.html on 09 Nov 2016
			 * says: "— Built-in Function: void * __builtin_return_address (unsigned int level) This function returns
			 * the return address of the current function, or of one of its callers. The level argument is number of
			 * frames to scan up the call stack. A value of 0 yields the return address of the current function, a value
			 * of 1 yields the return address of the caller of the current function, and so forth. When inlining the
			 * expected behavior is that the function returns the address of the function that is returned to. To work
			 * around this behavior use the noinline function attribute.
			 *
			 * The level argument must be a constant integer. On some machines it may be impossible to determine the
			 * return address of any function other than the current one; in such cases, or when the top of the stack
			 * has been reached, this function returns 0 or a random value. In addition, __builtin_frame_address may be
			 * used to determine if the top of the stack has been reached. Additional post-processing of the returned
			 * value may be needed, see __builtin_extract_return_addr. Calling this function with a nonzero argument can
			 * have unpredictable effects, including crashing the calling program. As a result, calls that are
			 * considered unsafe are diagnosed when the -Wframe-address option is in effect. Such calls should only be
			 * made in debugging situations."
			 *
			 * Current solution: replace call by a havocced aux variable.
			 */
			final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
			return constructOverapproximationForFunctionCall(main, loc, methodName, resultType);
			// } else if (methodName.equals("abs")) { // made obsolete by StdlibSupportInUltimate.java
			// throw new UnsupportedOperationException("function abs from stdlib.h not yet implemented");
		} else if ("__builtin_bswap32".equals(methodName)) {
			if (arguments.length != 1) {
				throw new IllegalArgumentException(methodName + MSG_ONLY_ONE_ARG);
			}
			main.dispatch(arguments[0]);
			final CPrimitive resultType = new CPrimitive(CPrimitives.UINT);
			return constructOverapproximationForFunctionCall(main, loc, methodName, resultType);
		} else if ("__builtin_bswap64".equals(methodName)) {
			if (arguments.length != 1) {
				throw new IllegalArgumentException(methodName + MSG_ONLY_ONE_ARG);
			}
			main.dispatch(arguments[0]);
			final CPrimitive resultType = new CPrimitive(CPrimitives.ULONG);
			return constructOverapproximationForFunctionCall(main, loc, methodName, resultType);
		} else {
			final FloatFunction floatFunction = FloatFunction.decode(methodName);
			if (floatFunction != null) {
				if (!FloatSupportInUltimate.getSupportedFloatOperations().contains(methodName)) {
					throw new AssertionError(
							"inconsistent information about supported float operations: " + methodName);
				}
				assert arguments.length == 1;
				final ExpressionResult arg = ((ExpressionResult) main.dispatch(arguments[0]))
						.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
				final CPrimitive typeDeterminedByName = floatFunction.getType();
				if (typeDeterminedByName != null) {
					mExpressionTranslation.convertFloatToFloat(loc, arg, typeDeterminedByName);
				}
				final RValue rvalue = mExpressionTranslation.constructOtherUnaryFloatOperation(loc, floatFunction,
						(RValue) arg.lrVal);
				final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(arg);
				result.lrVal = rvalue;
				return result;
			} else if (FloatSupportInUltimate.getUnsupportedFloatOperations().contains(methodName)) {
				final String msg = "Float math.h operation not supported " + methodName;
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return null;
		}
	}

	/**
	 * Construct an auxiliary variable that will be use as a substitute for a function call. The result will be marked
	 * as an overapproximation. If you overapproximate a function call, don't forget to dispatch the function call's
	 * arguments: the arguments may have side effects.
	 *
	 * @param functionName
	 *            the named of the function will be annotated to the overapproximation
	 * @param resultType
	 *            CType that determinies the type of the auxiliary variable
	 */
	private static ExpressionResult constructOverapproximationForFunctionCall(final Dispatcher main,
			final ILocation loc, final String functionName, final CType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		// introduce fresh aux variable
		final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		final ASTType astType = main.mTypeHandler.cType2AstType(loc, resultType);
		final VariableDeclaration tmpVarDecl = SFO.getTempVarVariableDeclaration(tmpId, astType, loc);
		builder.addDeclaration(tmpVarDecl);
		builder.putAuxVar(tmpVarDecl, loc);
		final IdentifierExpression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
		builder.addOverapprox(new Overapprox(functionName, loc));
		builder.setLRVal(new RValue(tmpVarIdExpr, resultType));
		return builder.build();
	}

	/**
	 * Construct assert statements that do memsafety checks for {@link pointerValue} if the corresponding settings are
	 * active. settings concerned are: - "Pointer base address is valid at dereference" - "Pointer to allocated memory
	 * at dereference"
	 */
	private static List<Statement> constructMemsafetyChecksForPointerExpression(final ILocation loc,
			final Expression pointerValue, final MemoryHandler memoryHandler,
			final AExpressionTranslation expressionTranslation) {
		final List<Statement> result = new ArrayList<>();

		if (memoryHandler.getPointerBaseValidityCheckMode() != PointerCheckMode.IGNORE) {

			// valid[s.base]
			final Expression validBase = memoryHandler.constructPointerBaseValidityCheck(loc, pointerValue);

			if (memoryHandler.getPointerBaseValidityCheckMode() == PointerCheckMode.ASSERTandASSUME) {
				final AssertStatement assertion = new AssertStatement(loc, validBase);
				final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
				chk.annotate(assertion);
				result.add(assertion);
			} else {
				assert memoryHandler.getPointerBaseValidityCheckMode() == PointerCheckMode.ASSUME : "missed a case?";
				final Statement assume = new AssumeStatement(loc, validBase);
				result.add(assume);
			}
		}
		if (memoryHandler.getPointerTargetFullyAllocatedCheckMode() != PointerCheckMode.IGNORE) {

			// s.offset < length[s.base])
			final Expression offsetSmallerLength = expressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_lessThan, MemoryHandler.getPointerOffset(pointerValue, loc),
					expressionTranslation.getCTypeOfPointerComponents(),
					ExpressionFactory.constructNestedArrayAccessExpression(loc, memoryHandler.getLengthArray(loc),
							new Expression[] { MemoryHandler.getPointerBaseAddress(pointerValue, loc) }),
					expressionTranslation.getCTypeOfPointerComponents());

			// s.offset >= 0;
			final Expression offsetNonnegative = expressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_greaterEqual, MemoryHandler.getPointerOffset(pointerValue, loc),
					expressionTranslation.getCTypeOfPointerComponents(),
					expressionTranslation.constructLiteralForIntegerType(loc,
							expressionTranslation.getCTypeOfPointerComponents(), new BigInteger("0")),
					expressionTranslation.getCTypeOfPointerComponents());

			final Expression aAndB =
					new BinaryExpression(loc, Operator.LOGICAND, offsetSmallerLength, offsetNonnegative);
			if (memoryHandler.getPointerBaseValidityCheckMode() == PointerCheckMode.ASSERTandASSUME) {
				final AssertStatement assertion = new AssertStatement(loc, aAndB);
				final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
				chk.annotate(assertion);
				result.add(assertion);
			} else {
				assert memoryHandler.getPointerBaseValidityCheckMode() == PointerCheckMode.ASSUME : "missed a case?";
				final Statement assume = new AssumeStatement(loc, aAndB);
				result.add(assume);
			}
		}
		return result;
	}

	/**
	 *
	 * The plan for function pointers: - every function f, that is used as a pointer in the C code gets a number #f - a
	 * pointer variable that points to a function then has the value {base: -1, offset: #f} - for every function f, that
	 * is used as a pointer, and that has a signature s, we introduce a "dispatch-procedure" in Boogie for s - the
	 * dispatch function for s = t1 x t2 x ... x tn -> t has the signature t1 x t2 x ... x tn x fp -> t, i.e., it takes
	 * the normal arguments, and a function address. When called, it calls the procedure that corresponds to the
	 * function address with the corresponding arguments and returns the returned value - a call to a function pointer
	 * is then translated to a call to the dispatch-procedure with fitting signature where the function pointer is given
	 * as additional argument - nb: when thinking about the function signatures, one has to keep in mind, the
	 * differences between C and Boogie, here. For instance, different C-function-signatures may correspond to on Boogie
	 * procedure signature, because a Boogie pointer does not know what it points to. Also, void types need special
	 * treatment as any pointer can be used as a void-pointer The special method CType.isCompatibleWith() is used for
	 * this. --> the names of the different dispatch function have to match exactly the classification done by
	 * isCompatibleWith.
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
		CType calledFuncType = funcNameRex.lrVal.getCType().getUnderlyingType();
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
				paramDecsFromCall[i] = new CDeclaration(rex.lrVal.getCType(), "#param" + i); // TODO:
				// SFO?
			}
			calledFuncCFunction = new CFunction(calledFuncCFunction.getResultType(), paramDecsFromCall,
					calledFuncCFunction.takesVarArgs());
		}

		// new Procedure()
		// functionSignaturesThatHaveAFunctionPointer = null;
		// TODO: use is compatible with instead of equals/set, make the name of the inserted procedure compatible to
		// isCompatibleWith
		final ProcedureSignature procSig = new ProcedureSignature(main, calledFuncCFunction);
		mFunctionSignaturesThatHaveAFunctionPointer.add(procSig);

		// String procName = calledFuncCFunction.functionSignatureAsProcedureName();
		final String procName = procSig.toString();

		final CFunction cFuncWithFP = addFPParamToCFunction(calledFuncCFunction);

		if (!mProcedures.containsKey(procName)) {
			addAProcedure(main, loc, null, procName, cFuncWithFP);
		}

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
			final String methodName) {
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
					mModifiedGlobalsIsUserDefined.add(methodName);
					final ModifiesSpecification ms = (ModifiesSpecification) spec[i];
					final LinkedHashSet<String> modifiedSet = new LinkedHashSet<>();
					for (final VariableLHS var : ms.getIdentifiers()) {
						modifiedSet.add(var.getIdentifier());
					}
					mModifiedGlobals.put(methodName, modifiedSet);
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
			final String methodName) {
		final CDeclaration[] paramDecs = cFun.getParameterTypes();
		final VarList[] in = new VarList[paramDecs.length];
		for (int i = 0; i < paramDecs.length; ++i) {
			final CDeclaration paramDec = paramDecs[i];

			final ASTType type;
			if (paramDec.getType() instanceof CArray) {
				// arrays are passed as pointers in C -- so we pass a Pointer in Boogie
				type = main.mTypeHandler.constructPointerType(loc);
			} else {
				type = main.mTypeHandler.cType2AstType(loc, paramDec.getType().getUnderlyingType());
			}

			final String paramId = main.mNameHandler.getInParamIdentifier(paramDec.getName(), paramDec.getType());
			in[i] = new VarList(loc, new String[] { paramId }, type);
			main.mCHandler.getSymbolTable().put(paramDec.getName(),
					new SymbolTableValue(paramId, null, paramDec, false, null, false));
		}
		updateCFunction(methodName, null, paramDecs, null, false);
		return in;
	}

	/**
	 * Creates local variables for in parameters.
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
		final VarList[] varListArray = mCurrentProcedure.getInParams();
		IASTNode[] paramDecs;
		if (varListArray.length == 0) {
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

		assert varListArray.length == paramDecs.length;
		for (int i = 0; i < paramDecs.length; ++i) {
			final VarList varList = varListArray[i];
			// final IASTParameterDeclaration paramDec = paramDecs[i];
			final IASTNode paramDec = paramDecs[i];
			for (final String bId : varList.getIdentifiers()) {
				final String cId = main.mCHandler.getSymbolTable().getCID4BoogieID(bId, loc);

				ASTType type = varList.getType();
				final CType cvar = main.mCHandler.getSymbolTable().get(cId, loc).getCVariable();

				// onHeap case for a function parameter means the parameter is
				// addressoffed in the function body
				boolean isOnHeap = false;
				if (main instanceof MainDispatcher) {
					isOnHeap = ((MainDispatcher) main).getVariablesForHeap().contains(paramDec);
				}

				// Copy of inparam that is writeable
				final String auxInvar = main.mNameHandler.getUniqueIdentifier(parent, cId, 0, isOnHeap, cvar);

				if (isOnHeap || cvar instanceof CArray) {
					type = main.mTypeHandler.constructPointerType(loc);
					((CHandler) main.mCHandler).addBoogieIdsOfHeapVars(auxInvar);
				}
				final VarList var = new VarList(loc, new String[] { auxInvar }, type);
				final VariableDeclaration inVarDecl =
						new VariableDeclaration(loc, new Attribute[0], new VarList[] { var });

				final VariableLHS tempLHS = new VariableLHS(loc, auxInvar);
				final IdentifierExpression rhsId = new IdentifierExpression(loc, bId);

				final ILocation igLoc = LocationFactory.createIgnoreLocation(loc);
				if (isOnHeap && !(cvar instanceof CArray)) {
					// we treat an array argument as a pointer -- thus no onHeap treatment here
					final LocalLValue llv = new LocalLValue(tempLHS, cvar);
					// malloc
					memoryHandler.addVariableToBeFreed(main, new LocalLValueILocationPair(llv, igLoc));
					// dereference
					final HeapLValue hlv = new HeapLValue(llv.getValue(), cvar);

					// convention: if a variable is put on heap or not, its ctype stays the same
					final ExpressionResult assign = ((CHandler) main.mCHandler).makeAssignment(main, igLoc, stmt, hlv,
							new RValue(rhsId, cvar), new ArrayList<Declaration>(),
							new LinkedHashMap<VariableDeclaration, ILocation>(), new ArrayList<Overapprox>());
					stmt.add(memoryHandler.getMallocCall(llv, igLoc));
					stmt.addAll(assign.stmt);
				} else {
					stmt.add(
							new AssignmentStatement(igLoc, new LeftHandSide[] { tempLHS }, new Expression[] { rhsId }));
				}
				assert main.mCHandler.getSymbolTable().containsCSymbol(cId);
				// Overwrite the information in the symbolTable for cId, s.t. it
				// points to the locally declared variable.
				main.mCHandler.getSymbolTable().put(cId,
						new SymbolTableValue(auxInvar, inVarDecl, new CDeclaration(cvar, cId), false, paramDec, false));
			}
		}
	}

	/**
	 * Update the map procedureToCFunctionType according to the given arguments If a parameter is null, the
	 * corresponding value will not be changed. (for takesVarArgs, use "false" to change nothing).
	 */
	private void updateCFunction(final String methodName, final CType returnType, final CDeclaration[] allParamDecs,
			final CDeclaration oneParamDec, final boolean takesVarArgs) {
		final CFunction oldCFunction = mProcedureToCFunctionType.get(methodName);

		final CType oldRetType = oldCFunction == null ? null : oldCFunction.getResultType();
		final CDeclaration[] oldInParams =
				oldCFunction == null ? new CDeclaration[0] : oldCFunction.getParameterTypes();
		final boolean oldTakesVarArgs = oldCFunction == null ? false : oldCFunction.takesVarArgs();

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

		mProcedureToCFunctionType.put(methodName, new CFunction(newRetType, newInParams, newTakesVarArgs));
	}

	/**
	 * Add a procedure to procedures according to a given CFunction. I.e. do a procedure declaration.
	 */
	private void addAProcedure(final Dispatcher main, final ILocation loc, final List<ACSLNode> contract,
			final String methodName, final CFunction funcType) {
		// begin new scope for retranslation of ACSL specification
		main.mCHandler.beginScope();

		final VarList[] in = processInParams(main, loc, funcType, methodName);

		// OUT VARLIST : only one out param in C
		VarList[] out = new VarList[1];

		final Attribute[] attr = new Attribute[0];
		final String[] typeParams = new String[0];
		Specification[] spec = makeBoogieSpecFromACSLContract(main, contract, methodName);

		if (funcType.getResultType() instanceof CPrimitive
				&& ((CPrimitive) funcType.getResultType()).getType() == CPrimitives.VOID
				&& !(funcType.getResultType() instanceof CPointer)) {
			if (mMethodsCalledBeforeDeclared.contains(methodName)) {
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
		if (!mModifiedGlobals.containsKey(methodName)) {
			mModifiedGlobals.put(methodName, new LinkedHashSet<String>());
		}
		if (!mCallGraph.containsKey(methodName)) {
			mCallGraph.put(methodName, new LinkedHashSet<String>());
		}

		Procedure proc = mProcedures.get(methodName);
		if (proc != null) {
			// combine the specification from the definition with the one from
			// the declaration
			final List<Specification> specFromDef = Arrays.asList(proc.getSpecification());
			final ArrayList<Specification> newSpecs = new ArrayList<>(Arrays.asList(spec));
			newSpecs.addAll(specFromDef);
			spec = newSpecs.toArray(new Specification[newSpecs.size()]);
			// TODO something else to take over for a declaration after the
			// definition?
		}
		proc = new Procedure(loc, attr, methodName, typeParams, in, out, spec, null);

		mProcedures.put(methodName, proc);
		updateCFunction(methodName, funcType.getResultType(), null, null, funcType.takesVarArgs());
		// end scope for retranslation of ACSL specification
		main.mCHandler.endScope();
	}

	/**
	 * Adds searchString to modifiedGlobals iff searchString is a global variable and the user has not defined a
	 * modifies clause.
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 *
	 * @param searchString
	 *            = boogieVarName!
	 * @param errLoc
	 *            the location for possible errors!
	 */
	public void checkIfModifiedGlobal(final SymbolTable symbTab, final String searchString, final ILocation errLoc) {
		String cName;
		if (!symbTab.containsBoogieSymbol(searchString)) {
			// temp variable!
			return;
		}
		cName = symbTab.getCID4BoogieID(searchString, errLoc);
		final String cId = mCurrentProcedure.getIdentifier();
		final SymbolTableValue stValue = symbTab.get(cName, errLoc);
		final CType cvar = stValue.getCVariable();
		if (cvar != null && stValue.getCDecl().isStatic()) {
			mModifiedGlobals.get(cId).add(searchString);
			return;
		}
		if (mModifiedGlobalsIsUserDefined.contains(cId)) {
			return;
		}
		final boolean isLocal;
		if (searchString.equals(SFO.RES)) {
			// this variable is reserved for the return variable and
			// therefore local!
			isLocal = true;
		} else {
			isLocal = !symbTab.get(cName, errLoc).isBoogieGlobalVar();
		}
		if (!isLocal) {
			// the variable is not local but could be a formal parameter
			if (!searchString.startsWith(SFO.IN_PARAM)) {
				// variable is global!
				mModifiedGlobals.get(cId).add(searchString);
			} else {
				assert false;
			}
		}
	}

	/**
	 * Checks, whether all procedures that are being called in C, were eventually declared within the C program.
	 *
	 * @return null if all called procedures were declared, otherwise the identifier of one procedure that was called
	 *         but not declared.
	 */
	private String isEveryCalledProcedureDeclared() {
		for (final String s : mMethodsCalledBeforeDeclared) {
			if (!mProcedures.containsKey(s)) {
				return s;
			}
		}
		return null;
	}

	void beginUltimateInitOrStart(final Dispatcher main, final ILocation loc, final String startOrInit) {
		main.mCHandler.beginScope();
		mCallGraph.put(startOrInit, new LinkedHashSet<String>());
		mCurrentProcedure = new Procedure(loc, new Attribute[0], startOrInit, new String[0], new VarList[0],
				new VarList[0], new Specification[0], null);
		mProcedures.put(startOrInit, mCurrentProcedure);
		mModifiedGlobals.put(mCurrentProcedure.getIdentifier(), new LinkedHashSet<String>());
	}

	void endUltimateInitOrStart(final Dispatcher main, final Procedure initDecl, final String startOrInit) {
		mProcedures.put(startOrInit, initDecl);
		main.mCHandler.endScope();
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

	public Result makeTheFunctionCallItself(final Dispatcher main, final ILocation loc, final String methodName,
			final List<Statement> stmt, final List<Declaration> decl, final Map<VariableDeclaration, ILocation> auxVars,
			final List<Overapprox> overappr, final List<Expression> args) {
		Expression expr = null;
		Statement call;
		if (mProcedures.containsKey(methodName)) {
			final VarList[] type = mProcedures.get(methodName).getOutParams();
			if (type.length == 0) { // void
				// C has only one return statement -> no need for forall
				call = new CallStatement(loc, false, new VariableLHS[0], methodName,
						args.toArray(new Expression[args.size()]));
			} else if (type.length == 1) { // one return value
				final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.RETURNED, null);
				expr = new IdentifierExpression(loc, tmpId);
				final VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpId, type[0].getType(), loc);
				auxVars.put(tmpVar, loc);
				decl.add(tmpVar);
				final VariableLHS tmpLhs = new VariableLHS(loc, tmpId);
				call = new CallStatement(loc, false, new VariableLHS[] { tmpLhs }, methodName,
						args.toArray(new Expression[args.size()]));
			} else { // unsupported!
				// String msg = "Cannot handle multiple out params! "
				// + loc.toString();
				// throw new IncorrectSyntaxException(loc, msg);
				return null; // FIXME ..
			}
		} else {
			mMethodsCalledBeforeDeclared.add(methodName);
			final String longDescription = "Return value of method '" + methodName
					+ "' unknown! Methods should be declared, before they are used! Return value assumed to be int ...";
			main.warn(loc, longDescription);
			final String ident = main.mNameHandler.getTempVarUID(SFO.AUXVAR.RETURNED, null);
			expr = new IdentifierExpression(loc, ident);

			// we don't know the CType of the returned value
			// we we INT
			final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);
			final VarList tempVar =
					new VarList(loc, new String[] { ident }, main.mTypeHandler.cType2AstType(loc, cPrimitive));
			final VariableDeclaration tmpVar =
					new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			final VariableLHS lhs = new VariableLHS(loc, ident);
			call = new CallStatement(loc, false, new VariableLHS[] { lhs }, methodName,
					args.toArray(new Expression[args.size()]));
		}
		stmt.add(call);
		final CType returnCType = mMethodsCalledBeforeDeclared.contains(methodName) ? new CPrimitive(CPrimitives.INT)
				: mProcedureToCFunctionType.get(methodName).getResultType().getUnderlyingType();
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, expr, returnCType, stmt);
		assert CHandler.isAuxVarMapcomplete(main.mNameHandler, decl, auxVars);
		return new ExpressionResult(stmt, new RValue(expr, returnCType), decl, auxVars, overappr);
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

	/**
	 * Getter for modified globals. Returns an unmodifiable map -- if you want to add something to the map, use the
	 * addModifiedGlobal(..) method
	 */
	public Map<String, LinkedHashSet<String>> getModifiedGlobals() {
		return Collections.unmodifiableMap(mModifiedGlobals);
	}

	public void addModifiedGlobal(final String procedureName, final String globVarName) {
		LinkedHashSet<String> set = mModifiedGlobals.get(procedureName);
		if (set == null) {
			set = new LinkedHashSet<>();
			mModifiedGlobals.put(procedureName, set);
		}
		set.add(globVarName);
	}

	/**
	 * Introduces an empty entry for a procedure in mModifiedGlobals.
	 *
	 * @param procedureName
	 */
	public void addModifiedGlobalEntry(final String procedureName) {
		LinkedHashSet<String> set = mModifiedGlobals.get(procedureName);
		if (set == null) {
			set = new LinkedHashSet<>();
			mModifiedGlobals.put(procedureName, set);
		}
	}

	/**
	 * @return procedures.
	 */
	public Map<String, Procedure> getProcedures() {
		return mProcedures;
	}

	/**
	 * @return the identifier of the current procedure.
	 */
	public String getCurrentProcedureID() {
		if (mCurrentProcedure == null) {
			return null;
		}
		return mCurrentProcedure.getIdentifier();
	}

	public boolean noCurrentProcedure() {
		return mCurrentProcedure == null;
	}

	public void addCallGraphEdge(final String source, final String target) {
		Set<String> set = mCallGraph.get(source);
		if (set == null) {
			set = new LinkedHashSet<>();
			mCallGraph.put(source, set);
		}
		set.add(target);
	}

	public void addCallGraphNode(final String node) {
		Set<String> set = mCallGraph.get(node);
		if (set == null) {
			set = new LinkedHashSet<>();
			mCallGraph.put(node, set);
		}
	}

	public CFunction getCFunctionType(final String function) {
		return mProcedureToCFunctionType.get(function);
	}

	public Set<ProcedureSignature> getFunctionsSignaturesWithFunctionPointers() {
		return Collections.unmodifiableSet(mFunctionSignaturesThatHaveAFunctionPointer);
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
