/*
 * Copyright (C) 2013-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.ASTNameCollector;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationResultReporter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager.BoogieProcedureInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction.VarArgsUsage;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Class that handles translation of functions.
 *
 * Note about modifies clauses:
 * <li>when an assignment is made, to a global variable, this must be registered with the function handler
 * (via/addModifies..)
 * <li>when a call is made, this must be registered with the function handler (via registerCall..) at the end of
 * translation the modifies clauses are updated according to the call graph and the modifications from each procedure
 *
 * @author Markus Lindenmann
 * @author Alexander Nutz
 */
public class FunctionHandler {

	/**
	 * Herein the function Signatures (as a CFunction) are stored for which a boogie procedure has to be created in the
	 * postProcessor that deals with the function pointer calls that can happen.
	 */
	private final LinkedHashSet<ProcedureSignature> mFunctionSignaturesThatHaveAFunctionPointer;

	private final ExpressionTranslation mExpressionTranslation;

	private final ProcedureManager mProcedureManager;

	private final ILogger mLogger;

	private final INameHandler mNameHandler;

	private final ITypeHandler mTypeHandler;

	private final CTranslationResultReporter mReporter;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final CHandler mCHandler;

	private final LocationFactory mLocationFactory;

	private final FlatSymbolTable mSymboltable;

	private final ExpressionResultTransformer mExprResultTransformer;

	private final Set<IASTNode> mVariablesOnHeap;

	/**
	 *
	 * @param logger
	 * @param nameHandler
	 * @param expressionTranslation
	 * @param procedureManager
	 * @param typeHandler
	 * @param reporter
	 * @param auxVarInfoBuilder
	 * @param chandler
	 * @param locFac
	 * @param symbolTable
	 * @param expressionResultTransformer
	 * @param variablesOnHeap
	 */
	public FunctionHandler(final ILogger logger, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final ProcedureManager procedureManager,
			final ITypeHandler typeHandler, final CTranslationResultReporter reporter,
			final AuxVarInfoBuilder auxVarInfoBuilder, final CHandler chandler, final LocationFactory locFac,
			final FlatSymbolTable symbolTable, final ExpressionResultTransformer expressionResultTransformer,
			final Set<IASTNode> variablesOnHeap) {
		mLogger = logger;
		mNameHandler = nameHandler;
		mExpressionTranslation = expressionTranslation;
		mProcedureManager = procedureManager;
		mTypeHandler = typeHandler;
		mReporter = reporter;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mCHandler = chandler;
		mLocationFactory = locFac;
		mFunctionSignaturesThatHaveAFunctionPointer = new LinkedHashSet<>();
		mSymboltable = symbolTable;
		mExprResultTransformer = expressionResultTransformer;
		mVariablesOnHeap = variablesOnHeap;
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
	public Result handleFunctionDeclarator(final IDispatcher main, final ILocation loc, final List<ACSLNode> contract,
			final CDeclaration cDec, final IASTDeclarator hook) {
		final String methodName = cDec.getName();
		final CFunction funcType = (CFunction) cDec.getType();

		registerFunctionDeclaration(main, loc, contract, methodName, funcType, hook);

		return new SkipResult();
	}

	/**
	 * Handles translation of IASTFunctionDefinition.
	 * <p>
	 * Notes about the architecture:
	 * <ul>
	 * <li>this method translates a function definition, as opposed to a declaration, so it has has body
	 * <li>the Result that is returned by this method is a Boogie procedure <b>implementation</b>
	 * <li>we also store a separate Boogie procedure <b>declaration</b> for each procedure
	 * <li>the procedure declarations are managed in this class, they are added to the Boogie program during post
	 * processing (i.e. at the end of CHandler.visit(IASTTranslationUnit ..) )
	 * <li>closing the modifies clauses transitively will be done during post processing, it only modifies the
	 * declarations
	 * </ul>
	 * <p>
	 * Note that a C function definition may have an ACSL specification while a Boogie procedure implementation does not
	 * have a specification (right?). Therefore we have to add any ACSL specs to the procedures member where the
	 * (Boogie) function declarations are stored.
	 * <p>
	 * The Result contains the Boogie procedure implementation.
	 *
	 * @param main
	 *            a reference to the main IDispatcher.
	 * @param node
	 *            the node to translate.
	 * @param contract
	 * @return the translation result.
	 */
	public Result handleFunctionDefinition(final IDispatcher main, final MemoryHandler memoryHandler,
			final IASTFunctionDefinition node, final CDeclaration cDec, final List<ACSLNode> contract) {

		final ILocation loc = mLocationFactory.createCLocation(node);
		final String definedProcName = cDec.getName();

		final BoogieProcedureInfo definedProcInfo = mProcedureManager.getOrConstructProcedureInfo(definedProcName);

		mProcedureManager.beginProcedureScope(mCHandler, definedProcInfo);

		final CFunction oldFunType = (CFunction) cDec.getType();
		final CFunction funType = updateVarArgsUsage(node, oldFunType);
		final CType returnCType = funType.getResultType();
		definedProcInfo.updateCFunction(funType);
		final boolean returnTypeIsVoid =
				returnCType instanceof CPrimitive && ((CPrimitive) returnCType).getType() == CPrimitives.VOID;

		VarList[] in = processInParams(loc, funType, definedProcInfo, node, true);
		if (isInParamVoid(in)) {
			// in-parameter is "void", as in "int foo(void) .." we normalize this to an empty list of in-parameters
			in = new VarList[0];
		}

		// There is only one return parameter in C, so this array always has size 1.
		VarList[] out = new VarList[1];
		final ASTType type = mTypeHandler.cType2AstType(loc, returnCType);

		if (returnTypeIsVoid) {
			// void, so there are no out vars
			out = new VarList[0];
		} else if (mProcedureManager.isCalledBeforeDeclared(definedProcInfo)) {
			// defaulting to int, when a method is called that is only declared later
			final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);
			out[0] = new VarList(loc, new String[] { SFO.RES }, mTypeHandler.cType2AstType(loc, cPrimitive));
		} else {
			// "normal case"
			assert type != null;
			out[0] = new VarList(loc, new String[] { SFO.RES }, type);
		}
		Specification[] spec = makeBoogieSpecFromACSLContract(main, contract, definedProcInfo);

		if (!definedProcInfo.hasDeclaration()) {
			// we have not seen this procedure yet, make a new declaration, register the procedure
			final Attribute[] attr = new Attribute[0];
			final String[] typeParams = new String[0];
			final Procedure proc = new Procedure(loc, attr, definedProcName, typeParams, in, out, spec, null);
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

			procDecl = new Procedure(procDecl.getLocation(), procDecl.getAttributes(), procDecl.getIdentifier(),
					procDecl.getTypeParams(), declIn, procDecl.getOutParams(), spec, null);

			definedProcInfo.resetDeclaration(procDecl);
		}

		// one more transformation of the declaration:
		{
			final Procedure proc = definedProcInfo.getDeclaration();
			final Procedure declWithCorrectlyNamedInParams = new Procedure(proc.getLocation(), proc.getAttributes(),
					proc.getIdentifier(), proc.getTypeParams(), in, proc.getOutParams(), proc.getSpecification(), null);
			definedProcInfo.resetDeclaration(declWithCorrectlyNamedInParams);
		}

		Body body;
		{
			/*
			 * The structure is as follows: <li> Preprocessing of the method body: - add new variables for parameters -
			 * havoc them - etc. (1) <li> dispatch body (2) <li> handle mallocs (3) <li> add statements and declarations
			 * to new body (4)
			 */
			final ExpressionResultBuilder bodyResultBuilder = new ExpressionResultBuilder();

			// 1)
			handleFunctionsInParams(main, loc, memoryHandler, bodyResultBuilder, node);
			// 2)
			final ExpressionResult bodyResult = (ExpressionResult) main.dispatch(node.getBody());
			bodyResultBuilder.addAllExceptLrValue(bodyResult);

			// 3) ,4)
			mCHandler.updateStmtsAndDeclsAtScopeEnd(bodyResultBuilder, node);

			assert bodyResultBuilder.getAuxVars().isEmpty();
			assert bodyResultBuilder.getOverappr().isEmpty();
			assert bodyResultBuilder.getLrValue() == null;

			body = mProcedureManager.constructBody(loc,
					bodyResultBuilder.getDeclarations()
							.toArray(new VariableDeclaration[bodyResultBuilder.getDeclarations().size()]),
					bodyResultBuilder.getStatements().toArray(new Statement[bodyResultBuilder.getStatements().size()]),
					mProcedureManager.getCurrentProcedureID());
		}

		final Procedure proc = definedProcInfo.getDeclaration();
		// Implementation -> Specification always null!
		final Procedure impl = new Procedure(loc, proc.getAttributes(), definedProcName, proc.getTypeParams(), in,
				proc.getOutParams(), null, body);

		mProcedureManager.endProcedureScope(mCHandler);

		return new Result(impl);
	}

	private static CFunction updateVarArgsUsage(final IASTFunctionDefinition node, final CFunction oldFunType) {
		final CFunction funType;
		// update varags usage
		if (oldFunType.hasVarArgs() && oldFunType.getVarArgsUsage() == VarArgsUsage.UNKNOWN) {
			// if the function body creates a va_list object it uses its varargs
			final ASTNameCollector vaListFinder = new ASTNameCollector("va_list");
			node.getBody().accept(vaListFinder);
			final boolean usesVarArgs = vaListFinder.getNames().length > 0;
			funType = oldFunType.updateVarArgsUsage(usesVarArgs);
		} else {
			funType = oldFunType;
		}
		return funType;
	}

	/**
	 * How we translate function pointers:
	 * <li>every function f, that is used as a pointer in the C code gets a number #f
	 * <li>a pointer variable that points to a function then has the value {base: -1, offset: #f}
	 * <li>for every function f, that is used as a pointer, and that has a signature s, we introduce a
	 * "dispatch-procedure" in Boogie for s
	 * <li>the dispatch-procedure for s = t1 x t2 x ... x tn -> t has the signature t1 x t2 x ... x tn x fp -> t, i.e.,
	 * it takes the normal arguments, and a function address. When called, it calls the procedure that corresponds to
	 * the function address with the corresponding arguments and returns the returned value
	 * <li>a call to a function pointer is then translated to a call to the dispatch-procedure with fitting signature
	 * where the function pointer is given as additional argument
	 * <li>note: when thinking about the function signatures, one has to keep in mind, the differences between C and
	 * Boogie, here. For instance, different C-function-signatures may correspond to on Boogie procedure signature,
	 * because a Boogie pointer does not know what it points to. Also, void types need special treatment as any pointer
	 * can be used as a void-pointer The special method CType.isCompatibleWith() is used for this. <br>
	 * --> the names of the different dispatch function have to precisely match the classification done by
	 * {@link CType.isCompatibleWith(..)).
	 *
	 * @param loc
	 * @param main
	 * @param functionPointer
	 * @param arguments
	 * @return
	 */
	private Result handleFunctionPointerCall(final ILocation loc, final IDispatcher main,
			final IASTExpression functionPointer, final IASTInitializerClause[] arguments) {
		assert functionPointer != null : "functionName is null";
		final ExpressionResult funcNameRex = (ExpressionResult) main.dispatch(functionPointer);

		CType calledFuncType = funcNameRex.getLrValue().getCType().getUnderlyingType();
		if (!(calledFuncType instanceof CFunction) && calledFuncType instanceof CPointer) {
			// .. because function pointers don't need to be dereferenced in
			// order to be called
			calledFuncType = ((CPointer) calledFuncType).getPointsToType().getUnderlyingType();
		}
		assert calledFuncType instanceof CFunction : "We need to unpack it further, right?";
		CFunction calledFuncCFunction = (CFunction) calledFuncType;

		// check if the function is declared without parameters -- then the
		// signature is determined by the (first) call
		if (calledFuncCFunction.getParameterTypes().length == 0 && arguments.length > 0) {
			final CDeclaration[] paramDecsFromCall = new CDeclaration[arguments.length];
			for (int i = 0; i < arguments.length; i++) {
				final ExpressionResult rex = (ExpressionResult) main.dispatch(arguments[i]);
				paramDecsFromCall[i] = new CDeclaration(rex.getLrValue().getCType(), "#param" + i); // TODO:
				// SFO?
			}
			calledFuncCFunction = calledFuncCFunction.newParameter(paramDecsFromCall);
		}

		// TODO: use CType.isCompatibleWith instead of equals/set, make the name of the inserted procedure compatible to
		// isCompatibleWith
		// TODO: DD 2017-11-23: Could we remove this collection of unknown symbols if we had a complete function symbol
		// table (perhaps collected in a prerun?)?
		final ProcedureSignature procSig = new ProcedureSignature(mTypeHandler, calledFuncCFunction);
		mFunctionSignaturesThatHaveAFunctionPointer.add(procSig);

		final String procName = procSig.toString();

		final CFunction cFuncWithFP = addFPParamToCFunction(calledFuncCFunction);

		registerFunctionDeclaration(main, loc, null, procName, cFuncWithFP, functionPointer);

		final IASTInitializerClause[] newArgs = new IASTInitializerClause[arguments.length + 1];
		System.arraycopy(arguments, 0, newArgs, 0, arguments.length);
		newArgs[newArgs.length - 1] = functionPointer;

		return handleFunctionCallGivenNameAndArguments(main, loc, procName, newArgs, functionPointer);
	}

	/**
	 * Handles translation of IASTFunctionCallExpression.
	 *
	 * @param main
	 *            a reference to the main IDispatcher.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleFunctionCallExpression(final IDispatcher main, final ILocation loc,
			final IASTExpression functionName, final IASTInitializerClause[] arguments) {
		if (!(functionName instanceof IASTIdExpression)) {
			return handleFunctionPointerCall(loc, main, functionName, arguments);
		}

		final String rawName = ((IASTIdExpression) functionName).getName().toString();
		// Resolve the function name (might be prefixed by multiparse)
		final String methodName = mSymboltable.applyMultiparseRenaming(functionName.getContainingFilename(), rawName);

		final SymbolTableValue nd = mSymboltable.findCSymbol(functionName, methodName);
		if (nd != null && !(nd.getDeclarationNode().getParent() instanceof IASTFunctionDefinition)) {
			// A 'real' function in the symbol table has a IASTFunctionDefinition as the parent of the declarator.
			return handleFunctionPointerCall(loc, main, functionName, arguments);
		}

		return handleFunctionCallGivenNameAndArguments(main, loc, methodName, arguments, functionName);
	}

	/**
	 * Handles translation of return statements.
	 *
	 * @param main
	 *            a reference to the main IDispatcher.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleReturnStatement(final IDispatcher main, final MemoryHandler memoryHandler,
			final IASTReturnStatement node) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		// The ReturnValue could be empty!
		final ILocation loc = mLocationFactory.createCLocation(node);
		final VarList[] outParams = mProcedureManager.getCurrentProcedureInfo().getDeclaration().getOutParams();

		if (mProcedureManager.isCalledBeforeDeclared(mProcedureManager.getCurrentProcedureInfo())
				&& mProcedureManager.getCurrentProcedureInfo().getDeclaration().getOutParams().length == 0) {
			// void method that was assumed to be returning int! -> return int
			final String id = outParams[0].getIdentifiers()[0];
			final VariableLHS lhs = ExpressionFactory.constructVariableLHS(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(outParams[0].getType()), id, new DeclarationInformation(
							StorageClass.IMPLEMENTATION_OUTPARAM, mProcedureManager.getCurrentProcedureID()));
			final Statement havoc = new HavocStatement(loc, new VariableLHS[] { lhs });

			resultBuilder.addStatement(havoc);
		} else if (node.getReturnValue() != null) {
			ExpressionResult returnValue = CTranslationUtil.convertExpressionListToExpressionResultIfNecessary(
					mExprResultTransformer, loc, main.dispatch(node.getReturnValue()), node);

			// functions cannot return arrays but only pointers
			returnValue = mCHandler.decayArrayToPointer(returnValue, loc, node);
			returnValue = mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(returnValue, loc, node);

			// do some implicit casts
			final CType functionResultType = mProcedureManager.getCurrentProcedureInfo().getCType().getResultType();
			// TODO 2018-09-22 Matthias: I have some doubts that the following lines are usefull.
			// Does C11 really mention a special treatment for zero literals in return statements?
			if (!returnValue.getLrValue().getCType().equals(functionResultType)
					&& functionResultType instanceof CPointer
					&& returnValue.getLrValue().getCType() instanceof CPrimitive
					&& returnValue.getLrValue().getValue() instanceof IntegerLiteral
					&& "0".equals(((IntegerLiteral) returnValue.getLrValue().getValue()).getValue())) {
				returnValue = new ExpressionResultBuilder().addAllExceptLrValue(returnValue)
						.setLrValue(new RValue(mExpressionTranslation.constructNullPointer(loc), functionResultType))
						.build();
			}

			if (outParams.length == 0) {
				// void method which is returning something! We remove the
				// return value!
				final String msg = "This method is declared to be void, but returning a value!";
				mReporter.syntaxError(loc, msg);
			} else if (outParams.length != 1) {
				final String msg = "We do not support several output parameters for functions";
				throw new UnsupportedSyntaxException(loc, msg);
			} else {
				final String id = outParams[0].getIdentifiers()[0];
				final VariableLHS lhs = ExpressionFactory.constructVariableLHS(loc,
						mTypeHandler.getBoogieTypeForCType(functionResultType), id, new DeclarationInformation(
								StorageClass.IMPLEMENTATION_OUTPARAM, mProcedureManager.getCurrentProcedureID()));
				final VariableLHS[] lhss = new VariableLHS[] { lhs };

				// Ugly workaround: Apply the conversion to the result of the
				// dispatched argument. On should first construct a copy of returnValueSwitched
				returnValue = mExprResultTransformer.convert(loc, returnValue, functionResultType);

				resultBuilder.addAllIncludingLrValue(returnValue);

				final RValue castExprResultRVal = (RValue) returnValue.getLrValue();
				resultBuilder.addStatement(StatementFactory.constructAssignmentStatement(loc, lhss,
						new Expression[] { castExprResultRVal.getValue() }));
				// assuming that we need no auxvars or overappr, here
			}
		}
		resultBuilder.addStatements(CTranslationUtil.createHavocsForAuxVars(resultBuilder.getAuxVars()));

		// we need to insert a free for each malloc of an auxvar before each return
		// frees are inserted in handleReturnStm
		for (final Entry<LocalLValueILocationPair, Integer> entry : memoryHandler.getVariablesToBeFreed().entrySet()) {
			if (entry.getValue() >= 1) {
				resultBuilder.addStatement(memoryHandler.getDeallocCall(entry.getKey().llv, entry.getKey().loc));

				resultBuilder.addStatement(
						new HavocStatement(loc, new VariableLHS[] { (VariableLHS) entry.getKey().llv.getLhs() }));
			}
		}

		resultBuilder.addStatement(new ReturnStatement(loc));
		return resultBuilder.build();
	}

	private Result handleFunctionCallGivenNameAndArguments(final IDispatcher main, final ILocation loc,
			final String calleeName, final IASTInitializerClause[] arguments, final IASTNode hook) {

		final BoogieProcedureInfo calleeProcInfo;
		if (!mProcedureManager.hasProcedure(calleeName)) {
			/*
			 * "implicit function declaration", assume it was declared as int foo(); (thus the signature can be
			 * completed by the first call, which we are dispatching here)
			 */
			mLogger.warn("implicit declaration of function " + calleeName);
			mProcedureManager.registerProcedure(calleeName);
			calleeProcInfo = mProcedureManager.getProcedureInfo(calleeName);
			calleeProcInfo.setDefaultDeclarationAndCType(loc,
					mTypeHandler.cType2AstType(loc, new CPrimitive(CPrimitives.INT)));
		} else {
			calleeProcInfo = mProcedureManager.getProcedureInfo(calleeName);
		}

		final Procedure calleeProcDecl = calleeProcInfo.getDeclaration();
		final CFunction calleeProcCType = calleeProcInfo.getCType();
		assert calleeProcDecl != null;
		if (calleeProcCType != null && calleeProcCType.hasVarArgs()) {
			if (calleeProcCType.isExtern()) {
				// we can handle calls to extern variadic functions by dispatching all the arguments and assuming a
				// non-deterministic return value. We do not need to declare the actual function.
				final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
				if (!calleeProcCType.getResultType().equals(new CPrimitive(CPrimitives.VOID))) {
					final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc,
							calleeProcCType.getResultType(), SFO.AUXVAR.NONDET);
					resultBuilder.addDeclaration(auxvarinfo.getVarDec());
					resultBuilder.addStatement(new HavocStatement(loc, new VariableLHS[] { auxvarinfo.getLhs() }));
					final LRValue returnValue = new RValue(auxvarinfo.getExp(), calleeProcCType.getResultType());
					resultBuilder.setLrValue(returnValue);
				}

				// dispatch all arguments
				for (final IASTInitializerClause arg : arguments) {
					final ExpressionResult argRes =
							mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arg);
					resultBuilder.addAllExceptLrValue(argRes);
				}
				return resultBuilder.build();
			}
			if (calleeProcCType.getVarArgsUsage() == VarArgsUsage.USED) {
				throw new UnsupportedSyntaxException(loc,
						"encountered a call to a var args function, var args are not supported at the moment: "
								+ calleeProcInfo.getProcedureName());
			}
			if (calleeProcCType.getVarArgsUsage() == VarArgsUsage.UNKNOWN) {
				// this should not happen, but just to be sure
				throw new UnsupportedSyntaxException(loc,
						"encountered a call to a var args function and varargs usage is unknown: "
								+ calleeProcInfo.getProcedureName());
			}
			// if the varargs are unused, we can just handle the function like any other function, but we need to
			// dispatch the varargs arguments separately and remove them from the actual call, so that the number of
			// parameters of the boogie procedure match
		}

		/*
		 * If in C a function is declared without input parameters, and no implementation has been given yet, the
		 * definitive signature is determined by the first call to the function.
		 */
		final boolean isCalleeSignatureNotYetDetermined =
				!calleeProcInfo.hasImplementation() && calleeProcDecl.getInParams().length == 0;
		checkNumberOfArguments(loc, calleeName, arguments, calleeProcDecl, calleeProcCType,
				isCalleeSignatureNotYetDetermined);
		// signature of the call and signature of the declaration match, continue
		// dispatch the inparams
		final ArrayList<Expression> translatedParams = new ArrayList<>();
		final ExpressionResultBuilder functionCallExpressionResultBuilder = new ExpressionResultBuilder();
		for (int i = 0; i < arguments.length; i++) {
			final IASTInitializerClause inParam = arguments[i];
			ExpressionResult in =
					mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, inParam);

			if (in.getLrValue().getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}

			if (isCalleeSignatureNotYetDetermined) {
				// add the current parameter to the procedure's signature
				calleeProcInfo.updateCFunctionAddParam(new CDeclaration(in.getLrValue().getCType(), SFO.IN_PARAM + i));
			} else if (calleeProcInfo.getCType() != null) {
				// we already know the parameters: do implicit casts and bool/int conversion
				if (i >= calleeProcCType.getParameterTypes().length
						&& calleeProcCType.getVarArgsUsage() == VarArgsUsage.UNUSED) {
					// only add the params if they are part of the signature or if the function uses its varargs
					functionCallExpressionResultBuilder.addAllExceptLrValue(in);
					continue;
				}
				CType expectedParamType =
						calleeProcInfo.getCType().getParameterTypes()[i].getType().getUnderlyingType();
				// bool/int conversion
				if (expectedParamType instanceof CPrimitive
						&& ((CPrimitive) expectedParamType).getGeneralType() == CPrimitiveCategory.INTTYPE
						|| expectedParamType instanceof CEnum) {
					in = mExprResultTransformer.rexBoolToIntIfNecessary(in, loc);
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
				in = mExprResultTransformer.convert(loc, in, expectedParamType);
			}

			translatedParams.add(in.getLrValue().getValue());
			functionCallExpressionResultBuilder.addAllExceptLrValue(in);
		}

		if (isCalleeSignatureNotYetDetermined) {
			/*
			 * This call determined the signature of the called function (it was declared without any parameters) Reset
			 * the declaration in our data structures.
			 */
			final VarList[] procParams = new VarList[calleeProcInfo.getCType().getParameterTypes().length];
			for (int i = 0; i < procParams.length; i++) {
				procParams[i] = new VarList(loc,
						new String[] { calleeProcInfo.getCType().getParameterTypes()[i].getName() },
						mTypeHandler.cType2AstType(loc, calleeProcInfo.getCType().getParameterTypes()[i].getType()));
			}
			final Procedure newProc = new Procedure(calleeProcDecl.getLocation(), calleeProcDecl.getAttributes(),
					calleeProcDecl.getIdentifier(), calleeProcDecl.getTypeParams(), procParams,
					calleeProcDecl.getOutParams(), calleeProcDecl.getSpecification(), calleeProcDecl.getBody());
			calleeProcInfo.resetDeclaration(newProc);
		}

		return makeTheFunctionCallItself(loc, calleeName, functionCallExpressionResultBuilder, translatedParams);
	}

	private static void checkNumberOfArguments(final ILocation loc, final String calleeName,
			final IASTInitializerClause[] arguments, final Procedure calleeProcDecl, final CFunction calleeProcCType,
			final boolean isCalleeSignatureNotYetDetermined) {
		if (isCalleeSignatureNotYetDetermined) {
			return;
		}
		if (arguments.length == calleeProcDecl.getInParams().length) {
			return;
		}
		if (calleeProcDecl.getInParams().length == 1 && calleeProcDecl.getInParams()[0].getType() == null
				&& arguments.length == 0) {
			return;
		}
		if (calleeProcCType.hasVarArgs()) {
			return;
		}
		throw new IncorrectSyntaxException(loc, "Function call has incorrect number of in-params: " + calleeName);
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
	private Specification[] makeBoogieSpecFromACSLContract(final IDispatcher main, final List<ACSLNode> contract,
			final BoogieProcedureInfo procInfo) {
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
				specList.addAll(Arrays.asList(resContr.getSpecs()));
			}
			spec = specList.toArray(new Specification[specList.size()]);
			for (int i = 0; i < spec.length; i++) {
				if (spec[i] instanceof ModifiesSpecification) {
					procInfo.setModifiedGlobalsIsUsedDefined(true);
					final ModifiesSpecification ms = (ModifiesSpecification) spec[i];
					final LinkedHashSet<VariableLHS> modifiedSet = new LinkedHashSet<>();
					for (final VariableLHS var : ms.getIdentifiers()) {
						modifiedSet.add(var);
					}
					procInfo.addModifiedGlobals(modifiedSet);
				}
			}
			// take care for behavior and completeness
			mCHandler.clearContract();
		}
		return spec;
	}

	/**
	 * Take the parameter information from the CDeclaration. Make a Varlist from it. Add the parameters to the
	 * symboltable. Also update procedureToParamCType member.
	 *
	 * @param updateSymbolTable
	 *            set this to true if the symbol table should be updated, false if only the result of this method is of
	 *            interest and side effects are unwanted
	 *
	 * @return
	 */
	private VarList[] processInParams(final ILocation loc, final CFunction cFun, final BoogieProcedureInfo procInfo,
			final IASTNode hook, final boolean updateSymbolTable) {
		final CDeclaration[] paramDecs = cFun.getParameterTypes();
		final VarList[] in = new VarList[paramDecs.length];
		for (int i = 0; i < paramDecs.length; ++i) {
			final CDeclaration currentParamDec = paramDecs[i];

			final ASTType currentParamType;
			if (currentParamDec.getType() instanceof CArray) {
				// arrays are passed as pointers in C -- so we pass a Pointer in Boogie
				currentParamType = mTypeHandler.constructPointerType(loc);
			} else {
				currentParamType = mTypeHandler.cType2AstType(loc, currentParamDec.getType().getUnderlyingType());
			}

			final String currentParamId =
					mNameHandler.getInParamIdentifier(currentParamDec.getName(), currentParamDec.getType());
			in[i] = new VarList(loc, new String[] { currentParamId }, currentParamType);

			if (updateSymbolTable) {
				final DeclarationInformation declInformation =
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procInfo.getProcedureName());

				mSymboltable.storeCSymbol(hook, currentParamDec.getName(),
						new SymbolTableValue(currentParamId, null, currentParamDec, declInformation, null, false));
			}
		}
		procInfo.updateCFunctionReplaceParams(paramDecs);
		return in;
	}

	/**
	 * Basic idea: For each of the procedure's input parameters we
	 * <li>create an auxiliary variable,
	 * <li>add code that initializes the auxiliary variable to the corresponding input parameter
	 *
	 * (note, alex, feb 18: I suppose this is because C allows changing of in parameters while Boogie does not, but
	 * would have to look it up to be sure)
	 *
	 * @param main
	 *            a reference to the main IDispatcher.
	 * @param loc
	 *            the location
	 * @param decl
	 *            the declaration list to append to.
	 * @param stmt
	 *            the statement list to append to.
	 * @param parent
	 */
	private void handleFunctionsInParams(final IDispatcher main, final ILocation loc, final MemoryHandler memoryHandler,
			// final ArrayList<Declaration> decl, final ArrayList<Statement> stmt,
			final ExpressionResultBuilder resultBuilder, final IASTFunctionDefinition parent) {
		final VarList[] inparamVarListArray =
				mProcedureManager.getCurrentProcedureInfo().getDeclaration().getInParams();
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
			final IASTNode paramDec = paramDecs[i];
			for (final String inparamBId : inparamVarList.getIdentifiers()) {
				final String inparamCId = mSymboltable.getCIdForBoogieId(inparamBId);

				ASTType type = inparamVarList.getType();
				final CType cvar = mSymboltable.findCSymbol(paramDec, inparamCId).getCType();

				// onHeap case for a function parameter means the parameter is
				// addressoffed in the function body
				boolean isOnHeap = false;
				if (main instanceof MainDispatcher) {
					isOnHeap = mVariablesOnHeap.contains(paramDec);
				}

				// Copy of inparam that is writeable
				final String inparamAuxVarName =
						mNameHandler.getUniqueIdentifier(parent, inparamCId, 0, isOnHeap, cvar);

				final DeclarationInformation inparamAuxVarDeclInfo = new DeclarationInformation(StorageClass.LOCAL,
						mProcedureManager.getCurrentProcedureInfo().getProcedureName());
				final BoogieType inParamAuxVarType = mTypeHandler.getBoogieTypeForBoogieASTType(type);

				if (isOnHeap || cvar instanceof CArray) {
					type = mTypeHandler.constructPointerType(loc);
					mCHandler.addBoogieIdsOfHeapVars(inparamAuxVarName);
				}
				final VarList var = new VarList(loc, new String[] { inparamAuxVarName }, type);
				final VariableDeclaration inVarDecl =
						new VariableDeclaration(loc, new Attribute[0], new VarList[] { var });

				/*
				 * note: because the writable aux var version of the inparam is added to the symbol table, which will
				 * trigger adding its declaration at endScope(), we do not add its declaration here!
				 *
				 * note: because the auxvars for the inparams do not need to be havocced, we do not need to add them
				 * here
				 */

				final IdentifierExpression rhsId = ExpressionFactory.constructIdentifierExpression(loc,
						inParamAuxVarType, inparamBId, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM,
								mProcedureManager.getCurrentProcedureInfo().getProcedureName()));

				final ILocation igLoc = LocationFactory.createIgnoreLocation(loc);
				if (isOnHeap && !(cvar instanceof CArray)) {
					final VariableLHS tempLHS = ExpressionFactory.constructVariableLHS(loc,
							mTypeHandler.getBoogiePointerType(), inparamAuxVarName, inparamAuxVarDeclInfo);
					// we treat an array argument as a pointer -- thus no onHeap treatment here
					final LocalLValue llv = new LocalLValue(tempLHS, cvar, null);
					// malloc
					memoryHandler.addVariableToBeFreed(new LocalLValueILocationPair(llv, igLoc));
					// dereference
					final HeapLValue hlv = LRValueFactory.constructHeapLValue(mTypeHandler, llv.getValue(), cvar, null);

					// convention (or rather an insight?): if a variable is put on heap or not, its ctype stays the same
					final ExpressionResult assign = mCHandler.makeAssignment(igLoc, hlv, Collections.emptyList(),
							new ExpressionResultBuilder().setLrValue(new RValue(rhsId, cvar)).build(), paramDec);

					resultBuilder.addStatement(memoryHandler.getMallocCall(llv, igLoc, paramDec));
					resultBuilder.addAllExceptLrValue(assign);
				} else {
					final VariableLHS tempLHS = ExpressionFactory.constructVariableLHS(loc, inParamAuxVarType,
							inparamAuxVarName, inparamAuxVarDeclInfo);
					resultBuilder.addStatement(StatementFactory.constructAssignmentStatement(igLoc,
							new LeftHandSide[] { tempLHS }, new Expression[] { rhsId }));
				}
				assert mSymboltable.containsCSymbol(paramDec, inparamCId);

				// Overwrite the information in the symbolTable for cId, s.t. it
				// points to the locally declared variable.
				mSymboltable.storeCSymbol(paramDec, inparamCId, new SymbolTableValue(inparamAuxVarName, inVarDecl,
						new CDeclaration(cvar, inparamCId), inparamAuxVarDeclInfo, paramDec, false));
			}
		}
	}

	/**
	 * Register a new procedure declaration in our internal data structures.
	 *
	 * @param main
	 * @param loc
	 * @param contract
	 *            may be null for empty contract
	 * @param methodName
	 * @param funcType
	 *            the signature of the corresponding C function
	 * @param node
	 */
	private void registerFunctionDeclaration(final IDispatcher main, final ILocation loc, final List<ACSLNode> contract,
			final String methodName, final CFunction funcType, final IASTNode node) {
		final BoogieProcedureInfo procInfo = mProcedureManager.getOrConstructProcedureInfo(methodName);

		// begin new scope for retranslation of ACSL specification
		mCHandler.beginScope();

		final VarList[] in = processInParams(loc, funcType, procInfo, node, false);

		// OUT VARLIST : only one out param in C
		VarList[] out = new VarList[1];

		final Attribute[] attr = new Attribute[0];
		final String[] typeParams = new String[0];
		Specification[] spec = makeBoogieSpecFromACSLContract(main, contract, procInfo);

		if (funcType.getResultType() instanceof CPrimitive
				&& ((CPrimitive) funcType.getResultType()).getType() == CPrimitives.VOID
				&& !(funcType.getResultType() instanceof CPointer)) {
			if (mProcedureManager.isCalledBeforeDeclared(procInfo)) {
				// this method was assumed to return int -> return int
				out[0] = new VarList(loc, new String[] { SFO.RES },
						new PrimitiveType(loc, BoogieType.TYPE_INT, SFO.INT));
			} else {
				// void, so there are no out vars
				out = new VarList[0];
			}
		} else {
			// we found a type, so node is type ASTType
			final ASTType type = mTypeHandler.cType2AstType(loc, funcType.getResultType());
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
		final Procedure newDeclaration =
				new Procedure(loc, attr, procInfo.getProcedureName(), typeParams, in, out, spec, null);

		procInfo.resetDeclaration(newDeclaration);

		// if possible, find the actual definition of this declaration s.t. we can update the varargs usage
		final CFunction newFuncType;
		if (node instanceof IASTDeclarator && funcType.hasVarArgs()
				&& funcType.getVarArgsUsage() == VarArgsUsage.UNKNOWN) {
			final IBinding binding = ((IASTDeclarator) node).getName().resolveBinding();
			final org.eclipse.cdt.internal.core.dom.parser.c.CFunction funBinding =
					(org.eclipse.cdt.internal.core.dom.parser.c.CFunction) binding;
			final IASTFunctionDeclarator definitionDeclarator = funBinding.getDefinition();
			if (definitionDeclarator != null) {
				final IASTFunctionDefinition def = (IASTFunctionDefinition) funBinding.getDefinition().getParent();
				newFuncType = updateVarArgsUsage(def, funcType);
			} else {
				newFuncType = funcType;
			}
		} else {
			newFuncType = funcType;
		}
		procInfo.updateCFunction(newFuncType);
		// end scope for retranslation of ACSL specification
		mCHandler.endScope();
	}

	/**
	 * FIXME: change the method name
	 *
	 * @param loc
	 * @param methodName
	 * @param functionCallERB
	 * @param translatedParameters
	 *
	 * @return
	 */
	Result makeTheFunctionCallItself(final ILocation loc, final String methodName,
			final ExpressionResultBuilder functionCallERB, final List<Expression> translatedParameters) {
		final Expression returnedValue;
		final Statement call;
		final BoogieProcedureInfo procInfo;
		if (mProcedureManager.hasProcedure(methodName)) {
			procInfo = mProcedureManager.getProcedureInfo(methodName);
			final VarList[] outParamVarlists = procInfo.getDeclaration().getOutParams();

			if (outParamVarlists.length == 0) {
				// void
				// C has only one return statement -> no need for forall
				call = StatementFactory.constructCallStatement(loc, false, new VariableLHS[0], methodName,
						translatedParameters.toArray(new Expression[translatedParameters.size()]));
				returnedValue = null;
			} else if (outParamVarlists.length == 1) {
				// one return value
				final ASTType astType = outParamVarlists[0].getType();
				final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, astType, SFO.AUXVAR.RETURNED);
				returnedValue = auxvar.getExp();
				final VariableLHS returnedValueAsLhs = auxvar.getLhs();
				functionCallERB.addAuxVar(auxvar);
				functionCallERB.addDeclaration(auxvar.getVarDec());

				call = StatementFactory.constructCallStatement(loc, false, new VariableLHS[] { returnedValueAsLhs },
						methodName, translatedParameters.toArray(new Expression[translatedParameters.size()]));
			} else {
				final String msg = "Cannot handle multiple out params! (makes no sense in the translation of a C "
						+ "program) " + loc.toString();
				throw new AssertionError(msg);
			}
		} else {
			procInfo = mProcedureManager.getOrConstructProcedureInfo(methodName);
			mProcedureManager.registerCalledBeforeDeclaredFunction(procInfo);

			final String longDescription = "Method was called before it was declared: '" + methodName
					+ "' unknown! Return value is assumed to be int ...";
			mReporter.warn(loc, longDescription);

			// we don't know the CType of the returned value we assume INT for now
			final CPrimitive cIntType = new CPrimitive(CPrimitives.INT);
			final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cIntType, SFO.AUXVAR.RETURNED);

			returnedValue = auxvar.getExp();

			functionCallERB.addDeclaration(auxvar.getVarDec());
			functionCallERB.addAuxVar(auxvar);

			call = StatementFactory.constructCallStatement(loc, false, new VariableLHS[] { auxvar.getLhs() },
					methodName, translatedParameters.toArray(new Expression[translatedParameters.size()]));
		}
		functionCallERB.addStatement(call);

		final CType returnCType = mProcedureManager.isCalledBeforeDeclared(procInfo) ? new CPrimitive(CPrimitives.INT)
				: procInfo.getCType().getResultType();

		if (returnedValue != null) {
			mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnedValue, returnCType, functionCallERB);
		}

		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, functionCallERB.getDeclarations(),
				functionCallERB.getAuxVars());

		if (returnedValue != null) {
			functionCallERB.setLrValue(new RValue(returnedValue, returnCType));
		}

		return functionCallERB.build();
	}

	public Set<ProcedureSignature> getFunctionsSignaturesWithFunctionPointers() {
		return Collections.unmodifiableSet(mFunctionSignaturesThatHaveAFunctionPointer);
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
		/*
		 * convention (necessary probably only because of here): typeHandler.ctype2boogietype yields "null" for
		 * CPrimitive(PRIMITIVE.VOID)
		 */
		return in.length == 1 && in[0].getType() == null;
	}

	private static CFunction addFPParamToCFunction(final CFunction calledFuncCFunction) {
		final CDeclaration[] newCDecs = new CDeclaration[calledFuncCFunction.getParameterTypes().length + 1];
		for (int i = 0; i < newCDecs.length - 1; i++) {
			newCDecs[i] = calledFuncCFunction.getParameterTypes()[i];
		}
		// FIXME string to SFO..?
		newCDecs[newCDecs.length - 1] = new CDeclaration(new CPointer(new CPrimitive(CPrimitives.VOID)), "#fp");

		return calledFuncCFunction.newParameter(newCDecs);
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
