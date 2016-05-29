/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Class caring for some post processing steps, like creating an initializer
 * procedure and the start procedure.
 * 
 * @author Markus Lindenmann
 * @date 12.10.2012
 */
public class PostProcessor {
	/**
	 * Holds the Boogie identifiers of the initialized global variables. Used
	 * for filling the modifies clause of Ultimate.start and Ultimate.init.
	 */
	private final LinkedHashSet<String> mInitializedGlobals;

	private final Dispatcher mDispatcher;
	private final ILogger mLogger;
	
	private final AExpressionTranslation mExpressionTranslation;

	/*
	 * Decides if the PostProcessor declares the special function that we use for
	 * converting Boogie-Real to a Boogie-Int.
	 * This is needed when we do a cast from float to int in C.
	 */
	public boolean mDeclareToIntFunction = false;

	/**
	 * Constructor.
	 */
	public PostProcessor(Dispatcher dispatcher, ILogger logger, AExpressionTranslation expressionTranslation) {
		mInitializedGlobals = new LinkedHashSet<String>();
		mDispatcher = dispatcher;
		mLogger = logger;
		mExpressionTranslation = expressionTranslation;
	}


	/**
	 * Start method for the post processing.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param loc
	 *            the location of the translation unit.
	 * @param memoryHandler 
	 * @param arrayHandler
	 *            a reference to the arrayHandler.
	 * @param structHandler 
	 * @param typeHandler 
	 * @param initStatements
	 *            a list of all global init statements.
	 * @param procedures
	 *            a list of all procedures in the TU.
	 * @param modifiedGlobals
	 *            modified globals for all procedures.
	 * @param undefinedTypes
	 *            a list of used, but not declared types.
	 * @param functions
	 *            a list of functions to add to the TU.
	 * @param mDeclarationsGlobalInBoogie 
	 * @param expressionTranslation 
	 * @param uninitGlobalVars
	 *            a set of uninitialized global variables.
	 * @return a declaration list holding the init() and start() procedure.
	 */
	public ArrayList<Declaration> postProcess(Dispatcher main, ILocation loc, MemoryHandler memoryHandler, 
			ArrayHandler arrayHandler, FunctionHandler functionHandler, StructHandler structHandler,
			TypeHandler typeHandler, Set<String> undefinedTypes, 
			LinkedHashMap<Declaration,CDeclaration> mDeclarationsGlobalInBoogie, AExpressionTranslation expressionTranslation) {
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		decl.addAll(declareUndefinedTypes(loc, undefinedTypes));
		decl.addAll(createUltimateInitProcedure(loc, main, memoryHandler, arrayHandler, functionHandler, structHandler,
				mDeclarationsGlobalInBoogie, expressionTranslation));
		decl.addAll(createUltimateStartProcedure(main, loc, functionHandler));
		decl.addAll(declareFunctionPointerProcedures(main, functionHandler, memoryHandler, structHandler));
		decl.addAll(declareConversionFunctions(main, functionHandler, memoryHandler, structHandler));
		
		if (!(typeHandler).useIntForAllIntegerTypes()) {
			decl.addAll(PostProcessor.declarePrimitiveDataTypeSynonyms(loc, main.getTypeSizes(),
					typeHandler));

			if ((typeHandler).areFloatingTypesNeeded()) {
				decl.addAll(PostProcessor.declareFloatDataTypes(loc, main.getTypeSizes(), typeHandler));
			}

		}
		return decl;
	}
	
	private ArrayList<Declaration> declareConversionFunctions(
			Dispatcher main, FunctionHandler functionHandler, 
			MemoryHandler memoryHandler, StructHandler structHandler) {

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final ArrayList<Declaration> decls = new ArrayList<>();
		
		
		// function to_int
		final String inReal = "inReal";
//		IdentifierExpression inRealIdex = new IdentifierExpression(ignoreLoc, inReal);
		final String outInt = "outInt";
//		IdentifierExpression outIntIdex = new IdentifierExpression(ignoreLoc, outInt);
		final VarList realParam = new VarList(ignoreLoc, new String[] {  }, new PrimitiveType(ignoreLoc, SFO.REAL));
		final VarList[] oneRealParam = new VarList[] { realParam };
		final VarList intParam = new VarList(ignoreLoc, new String[] { outInt }, new PrimitiveType(ignoreLoc, SFO.INT));
//		VarList[] oneIntParam = new VarList[] { intParam };
//		Expression inRealGeq0 = new BinaryExpression(ignoreLoc, 
//				BinaryExpression.Operator.COMPGEQ, inRealIdex, new IntegerLiteral(ignoreLoc, SFO.NR0));
//		
//		Expression roundDown = new BinaryExpression(ignoreLoc, BinaryExpression.Operator.LOGICAND,
//				new BinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLEQ, 
//						new BinaryExpression(ignoreLoc, BinaryExpression.Operator.ARITHMINUS, inRealIdex, new IntegerLiteral(ignoreLoc, SFO.NR1)),
//						outIntIdex),
//				new BinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLEQ, 
//						outIntIdex,
//						inRealIdex));
//		Expression roundUp = new BinaryExpression(ignoreLoc, BinaryExpression.Operator.LOGICAND,
//				new BinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLEQ, 
//						inRealIdex,
//						outIntIdex),
//			new BinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLEQ, 
//						new BinaryExpression(ignoreLoc, BinaryExpression.Operator.ARITHPLUS, inRealIdex, new IntegerLiteral(ignoreLoc, SFO.NR1)),
//						outIntIdex));
//			
//		Specification toIntSpec = new EnsuresSpecification(ignoreLoc, false, new IfThenElseExpression(ignoreLoc, inRealGeq0, roundDown, roundUp));
//		decls.add(new Procedure(ignoreLoc, new Attribute[0], SFO.TO_INT, new String[0], oneRealParam, oneIntParam, new Specification[] { toIntSpec }, null));

		if (mDeclareToIntFunction ) {
			decls.add(new FunctionDeclaration(ignoreLoc, new Attribute[0], SFO.TO_INT, new String[0], oneRealParam, intParam));
		}

		return decls;
	}

	private ArrayList<Declaration> declareFunctionPointerProcedures(
			Dispatcher main, FunctionHandler functionHandler, 
			MemoryHandler memoryHandler, StructHandler structHandler) {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ArrayList<Declaration> result = new ArrayList<>();
//		for (CFunction cFunc : functionHandler.functionSignaturesThatHaveAFunctionPointer) {
		for (final ProcedureSignature cFunc : functionHandler.functionSignaturesThatHaveAFunctionPointer) {
//			String procName = cFunc.functionSignatureAsProcedureName();
			final String procName = cFunc.toString();
			
			final VarList[] inParams = functionHandler.getProcedures().get(procName).getInParams();
			final VarList[] outParams = functionHandler.getProcedures().get(procName).getOutParams();
			assert outParams.length <= 1;
			final Procedure functionPointerMuxProc = new Procedure(ignoreLoc, new Attribute[0], 
					procName, 
					new String[0], 
					inParams, 
					outParams, 
//					FIXME: it seems an odd convention that giving it "null" as Specification makes it an implementation 
					//(instead of a procedure) in Boogie
//					new Specification[0], 
					null, 
					functionHandler.getFunctionPointerFunctionBody(ignoreLoc, main, memoryHandler, structHandler, procName, cFunc, inParams, outParams));
			result.add(functionPointerMuxProc);
		}
		return result;
	}


	/**
	 * Declares a type for each identifier in the set.
	 * 
	 * @param loc
	 *            the location to be used for the declarations.
	 * @param undefinedTypes
	 *            a list of undefined, but used types.
	 * @return a list of type declarations.
	 */
	private static Collection<? extends Declaration> declareUndefinedTypes(
			final ILocation loc, final Set<String> undefinedTypes) {
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		for (final String s : undefinedTypes) {
			decl.add(new TypeDeclaration(loc, new Attribute[0], false, s,
					new String[0]));
		}
		return decl;
	}

	/**
	 * Create the Ultimate initializer procedure for global variables.
	 * 
	 * @param translationUnitLoc
	 *            the location of the translation unit. declaration.
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param memoryHandler 
	 * @param arrayHandler
	 *            a reference to the arrayHandler.
	 * @param structHandler 
	 * @param declarationsGlobalInBoogie 
	 * @param initStatements
	 *            a list of all global init statements.
	 * @param uninitGlobalVars
	 *            a set of uninitialized global variables.
	 * @return a list the initialized variables.
	 */
	private ArrayList<Declaration> createUltimateInitProcedure(ILocation translationUnitLoc,
			Dispatcher main, MemoryHandler memoryHandler, ArrayHandler arrayHandler, FunctionHandler functionHandler,   
			StructHandler structHandler, LinkedHashMap<Declaration, CDeclaration> declarationsGlobalInBoogie, 
			AExpressionTranslation expressionTranslation) {
		functionHandler.beginUltimateInit(main, translationUnitLoc, SFO.INIT);
		final ArrayList<Statement> initStatements = new ArrayList<Statement>();

		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<VariableDeclaration> initDecl = new ArrayList<VariableDeclaration>();
		if (main.isMMRequired() || memoryHandler.getRequiredMemoryModelFeatures().isMemoryModelInfrastructureRequired()) {
			if (memoryHandler.getRequiredMemoryModelFeatures().isMemoryModelInfrastructureRequired()) {
				final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(
						translationUnitLoc, mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
				final LeftHandSide[] lhs = new LeftHandSide[] { new ArrayLHS(translationUnitLoc,
						new VariableLHS(translationUnitLoc, SFO.VALID),
						new Expression[] { zero }) };
				final Expression[] rhs = new Expression[] { memoryHandler.getBooleanArrayHelper().constructFalse() };
				initStatements.add(0, new AssignmentStatement(translationUnitLoc, lhs, rhs));
				mInitializedGlobals.add(SFO.VALID);
			}

			final VariableLHS slhs = new VariableLHS(translationUnitLoc, SFO.NULL);
			initStatements.add(0, new AssignmentStatement(translationUnitLoc, 
					new LeftHandSide[] { slhs }, 
					new Expression[] { new StructConstructor(translationUnitLoc, new String[]{"base", "offset"}, 
							new Expression[]{
							expressionTranslation.constructLiteralForIntegerType(translationUnitLoc, expressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO),
							expressionTranslation.constructLiteralForIntegerType(translationUnitLoc, expressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO)
							})}));
			mInitializedGlobals.add(SFO.NULL);
		}
		for (final Statement stmt : initStatements) {
			if (stmt instanceof AssignmentStatement) {
				final AssignmentStatement ass = (AssignmentStatement) stmt;
				assert ass.getLhs().length == 1; // by construction ...
				final LeftHandSide lhs = ass.getLhs()[0];
				final String id = BoogieASTUtil.getLHSId(lhs);
				mInitializedGlobals.add(id);
			}
		}

		//initialization for statics and other globals
		for (final Entry<Declaration, CDeclaration> en : declarationsGlobalInBoogie.entrySet()) {
			if (en.getKey() instanceof TypeDeclaration || en.getKey() instanceof ConstDeclaration) {
				continue;
			}
			final ILocation currentDeclsLoc = en.getKey().getLocation();
			final ExpressionResult initializer = en.getValue().getInitializer();
			
			/*
			 * global variables with external linkage are not implicitly initialized. (They are initialized by 
			 * the module that provides them..)
			 */
//			if (main.cHandler.getSymbolTable().get(en.getValue().getName(), currentDeclsLoc).isExtern())
			if (en.getValue().isExtern()) {
				continue;
			}

			for (final VarList vl  : ((VariableDeclaration) en.getKey()).getVariables()) {
				for (final String id : vl.getIdentifiers()) {
					if (main.mCHandler.isHeapVar(id)) {
						final LocalLValue llVal = new LocalLValue(new VariableLHS(currentDeclsLoc, id), en.getValue().getType());
						initStatements.add(memoryHandler.getMallocCall(main, functionHandler, 
								llVal, currentDeclsLoc));
					}

					//					if (initializer != null) {
					//						assert ((VariableDeclaration)en.getKey()).getVariables().length == 1 
					//								&& ((VariableDeclaration)en.getKey()).getVariables()[0].getIdentifiers().length == 1;
					final ExpressionResult initRex = 
							main.mCHandler.getInitHandler().initVar(currentDeclsLoc, main, 
									new VariableLHS(currentDeclsLoc, id), en.getValue().getType(), initializer);
					initStatements.addAll(initRex.stmt);
					initStatements.addAll(CHandler.createHavocsForAuxVars(initRex.auxVars));
					for (final Declaration d : initRex.decl)
					 {
						initDecl.add((VariableDeclaration) d);
					//					} else { //no initializer --> default initialization
					//						ResultExpression nullInitializer = main.cHandler.getInitHandler().initVar(loc, main, 
					//								new VariableLHS(loc, id), en.getValue().getType(), null) ;
					//
					//						initStatements.addAll(nullInitializer.stmt);
					//						initStatements.addAll(CHandler.createHavocsForNonMallocAuxVars(nullInitializer.auxVars));
					//						for (Declaration d : nullInitializer.decl)
					//							initDecl.add((VariableDeclaration) d);
					//					}
					}
				}
			}
			for (final VarList vl  : ((VariableDeclaration) en.getKey()).getVariables()) {
				mInitializedGlobals.addAll(Arrays.asList(vl.getIdentifiers()));
			}
		}

		mInitializedGlobals.addAll(functionHandler.getModifiedGlobals().get(SFO.INIT));

		final Specification[] specsInit = new Specification[1];

		final VariableLHS[] modifyList = new VariableLHS[mInitializedGlobals.size()];
		int i = 0;
		for (final String var: mInitializedGlobals) {
			modifyList[i++] = new VariableLHS(translationUnitLoc, var);
		}
		specsInit[0] = new ModifiesSpecification(translationUnitLoc, false, modifyList);
		final Procedure initProcedureDecl = new Procedure(translationUnitLoc, new Attribute[0], SFO.INIT, new String[0],
				new VarList[0], new VarList[0], specsInit, null);
		final Body initBody = new Body(translationUnitLoc,
				initDecl.toArray(new VariableDeclaration[0]),
				initStatements.toArray(new Statement[0]));
		decl.add(new Procedure(translationUnitLoc, new Attribute[0], SFO.INIT, new String[0],
				new VarList[0], new VarList[0], null, initBody));

		functionHandler.endUltimateInit(main, initProcedureDecl, SFO.INIT);
		return decl;
	}



	/**
	 * Create the Ultimate start procedure, calling the init method, and the
	 * checked method (defined in an Eclipse setting).
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * 
	 * @param loc
	 *            the location of the translation unit.
	 * @param procedures
	 *            a list of all procedures in the TU.
	 * @param modifiedGlobals
	 *            modified globals for all procedures.
	 * @return declarations and implementation of the start procedure.
	 */
	private ArrayList<Declaration> createUltimateStartProcedure(
			Dispatcher main, ILocation loc, FunctionHandler functionHandler) {
		final LinkedHashMap<String, Procedure> procedures = functionHandler.getProcedures();
		final String checkedMethod = main.getCheckedMethod();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();

		if (!checkedMethod.equals(SFO.EMPTY)
				&& procedures.containsKey(checkedMethod)) {
			mLogger.info("Settings: Checked method=" + checkedMethod);

			final LinkedHashMap<String, LinkedHashSet<String>> modifiedGlobals = functionHandler.getModifiedGlobals();
			functionHandler.beginUltimateInit(main, loc, SFO.START);
			
			Procedure startDeclaration = null;
			Specification[] specsStart = new Specification[0];

			if (!functionHandler.getCallGraph().containsKey(SFO.START)) {
				functionHandler.getCallGraph().put(SFO.START, new LinkedHashSet<String>());
			}
			functionHandler.getCallGraph().get(SFO.START).add(SFO.INIT);

			functionHandler.getCallGraph().get(SFO.START).add(checkedMethod);

			final ArrayList<Statement> startStmt = new ArrayList<Statement>();
			final ArrayList<VariableDeclaration> startDecl = new ArrayList<VariableDeclaration>();
			specsStart = new Specification[1];
			startStmt.add(new CallStatement(loc, false, new VariableLHS[0],
					SFO.INIT, new Expression[0]));
			final VarList[] checkedMethodOutParams = procedures.get(checkedMethod).getOutParams();
			final VarList[] checkedMethodInParams = procedures.get(checkedMethod).getInParams();
			final Specification[] checkedMethodSpec = procedures.get(checkedMethod).getSpecification();

			//find out the requires specs of the checked method and assume it before its start
			final ArrayList<Statement> reqSpecsAssumes = new ArrayList<>();
			for (final Specification spec : checkedMethodSpec) {
				if (spec instanceof RequiresSpecification) {
					reqSpecsAssumes.add(
							new AssumeStatement(loc, 
									((RequiresSpecification) spec).getFormula()));
				}
			}
			startStmt.addAll(reqSpecsAssumes);
			
			final ArrayList<Expression> args = new ArrayList<Expression>();
			if (checkedMethodInParams.length > 0) {
				startDecl
				.add(new VariableDeclaration(loc, new Attribute[0], checkedMethodInParams));
				for (final VarList arg : checkedMethodInParams) {
					assert arg.getIdentifiers().length == 1; // by construction
					final String id = arg.getIdentifiers()[0];
					args.add(new IdentifierExpression(loc, id));
				}
			}
			if (checkedMethodOutParams.length != 0) {
				assert checkedMethodOutParams.length == 1;
				// there is 1(!) return value
				final String checkMethodRet = main.mNameHandler
						.getTempVarUID(SFO.AUXVAR.RETURNED, null);
				main.mCHandler.getSymbolTable().addToReverseMap(checkMethodRet,
						SFO.NO_REAL_C_VAR + checkMethodRet, loc);
				final VarList tempVar = new VarList(loc,
						new String[] { checkMethodRet }, checkedMethodOutParams[0].getType());
				final VariableDeclaration tmpVar = new VariableDeclaration(loc,
						new Attribute[0], new VarList[] { tempVar });
				startDecl.add(tmpVar);
				startStmt.add(new CallStatement(loc, false,
						new VariableLHS[] { new VariableLHS(loc, checkMethodRet) }, 
						checkedMethod, args.toArray(new Expression[0])));
			} else { // void
				startStmt.add(new CallStatement(loc, false, new VariableLHS[0],
						checkedMethod, args.toArray(new Expression[0])));
			}

			final LinkedHashSet<VariableLHS> startModifiesClause = new LinkedHashSet<VariableLHS>();
			for (final String id: mInitializedGlobals) {
				startModifiesClause.add(new VariableLHS(loc, id));
			}
			//			if (mSomethingOnHeapIsInitialized) {
			//				for (String t : new String[] { SFO.INT, SFO.POINTER,
			//						SFO.REAL/*, SFO.BOOL */}) {
			//					startModifiesClause.add(new VariableLHS(loc, SFO.MEMORY + "_" + t));
			//				}		
			//			}
			for (final String id: modifiedGlobals.get(checkedMethod)) {
				startModifiesClause.add(new VariableLHS(loc, id));
			}
			specsStart[0] = new ModifiesSpecification(loc, false,
					startModifiesClause.toArray(new VariableLHS[0]));

			final Body startBody = new Body(loc,
					startDecl.toArray(new VariableDeclaration[0]),
					startStmt.toArray(new Statement[0]));
			decl.add(new Procedure(loc, new Attribute[0], SFO.START,
					new String[0], new VarList[0], new VarList[0], null,
					startBody));

			//		} else if (!checkMethod.equals(SFO.EMPTY) //alex, 28.5.2014: this should be obsolete as in this case, DetermineNecessaryDeclarations should have made the warning
			//				&& !procedures.containsKey(checkMethod)) {
			//			String msg = "You specified the starting procedure: "
			//					+ checkMethod
			//					+ "\n The program does not have this method. ULTIMATE will continue in library mode (i.e., each procedure can be starting procedure and global variables are not initialized).";
			//			Dispatcher.warn(loc, msg);
			
			startDeclaration = new Procedure(loc, new Attribute[0], SFO.START,
					new String[0], new VarList[0], new VarList[0], specsStart,
					null);
			functionHandler.endUltimateInit(main, startDeclaration, SFO.START);
		} else {
			mLogger.info("Settings: Library mode!");
			if (procedures.containsKey("main")) {
				final String msg = "You selected the library mode (i.e., each procedure can be starting procedure and global variables are not initialized). This program contains a \"main\" procedure. Maybe you wanted to select the \"main\" procedure as starting procedure.";
				mDispatcher.warn(loc, msg);
			}
		}
		return decl;
	}
	
	/**
	 * Generate type declarations like, e.g., the following.   
	 *     type { :isUnsigned true } { :bitsize 16 } C_USHORT = bv16;
	 * This allow us to use type synonyms like C_USHORT during the translation.
	 * This is yet not consequently implemented.
	 * This is desired not only for bitvectors: it makes our translation more
	 * modular and can ease debugging.
	 * However, that this located in this class and fixed to bitvectors is a
	 * workaround.
	 * @param typeHandler 
	 */
	public static ArrayList<Declaration> declarePrimitiveDataTypeSynonyms(ILocation loc, 
			TypeSizes typeSizes, TypeHandler typeHandler) {
		final ArrayList<Declaration> decls = new ArrayList<Declaration>();
		for (final CPrimitive.PRIMITIVE cPrimitive: CPrimitive.PRIMITIVE.values()) {
			final CPrimitive cPrimitiveO = new CPrimitive(cPrimitive);
			if (cPrimitiveO.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
				final Attribute[] attributes = new Attribute[2];
				attributes[0] = new NamedAttribute(loc, "isUnsigned", 
						new Expression[]{ new BooleanLiteral(loc, cPrimitiveO.isUnsigned())});
				final int bytesize = typeSizes.getSize(cPrimitive);
				final int bitsize = bytesize * 8;
				attributes[1] = new NamedAttribute(loc, "bitsize", 
						new Expression[]{ new IntegerLiteral(loc, String.valueOf(bitsize))});
				final String identifier = "C_" + cPrimitive.name();
				final String[] typeParams = new String[0];
				final String name= "bv" + bitsize;
				final ASTType astType = typeHandler.bytesize2asttype(loc, GENERALPRIMITIVE.INTTYPE, bytesize);
				decls.add(new TypeDeclaration(loc, attributes, false, identifier, typeParams , astType));
			}
		}
		return decls;
	}

	/**
	 * Generate FloatingPoint types
	 * @param loc
	 * @param typesizes
	 * @param typeHandler
	 * @return
	 */
	public static ArrayList<Declaration> declareFloatDataTypes(ILocation loc,
			TypeSizes typesizes, TypeHandler typeHandler) {
		final ArrayList<Declaration> decls = new ArrayList<Declaration>();
		
		//Roundingmodes, for now RNE hardcoded
		
		final Attribute[] attributesRM = new Attribute[1];
		attributesRM[0] = new NamedAttribute(loc, FunctionDeclarations.s_BUILTIN_IDENTIFIER, new Expression[]{new StringLiteral(loc, "RoundingMode")});
		final String identifierRM = "RoundingMode";
		final String[] typeParamsRM = new String[0];
		decls.add(new TypeDeclaration(loc, attributesRM, false, identifierRM, typeParamsRM));
		
		final Attribute attributeRNE = new NamedAttribute(loc, FunctionDeclarations.s_BUILTIN_IDENTIFIER, new Expression[]{new StringLiteral(loc, "RNE")});
		
		decls.add(new ConstDeclaration(loc, new Attribute[]{attributeRNE}, false, new VarList(loc, new String[]{"RNE"}, new NamedType(loc, "RoundingMode", new ASTType[0])),null, false));
		
		for (final CPrimitive.PRIMITIVE cPrimitive: CPrimitive.PRIMITIVE.values()) {
			
			final CPrimitive cPrimitive0 = new CPrimitive(cPrimitive);
			
			if (cPrimitive0.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE
					&& !cPrimitive0.isComplexType()) {
				final Attribute[] attributes = new Attribute[2];
				attributes[0] = new NamedAttribute(loc, FunctionDeclarations.s_BUILTIN_IDENTIFIER, new Expression[]{new StringLiteral(loc, "FloatingPoint")});
				final int bytesize = typesizes.getSize(cPrimitive);
				final int[] indices = new int[2];
				switch (bytesize) {
					case 4:
						indices[0] = 8;
						indices[1] = 24;
						break;
					case 8:
						indices[0] = 11;
						indices[1] = 53;
						break;
					case 12: // because of 80bit long doubles on linux x86
					case 16:
						indices[0] = 15;
						indices[1] = 113;
						break;
					default:
						throw new UnsupportedSyntaxException(loc, "unknown primitive type");
				}
				attributes[1] = new NamedAttribute(loc, FunctionDeclarations.s_INDEX_IDENTIFIER,
						new Expression[]{	new IntegerLiteral(loc, String.valueOf(indices[0])),
											new IntegerLiteral(loc, String.valueOf(indices[1]))});
				final String identifier = "C_" + cPrimitive.name();
				final String[] typeParams = new String[0];
				decls.add(new TypeDeclaration(loc, attributes, false, identifier, typeParams ));
				
			}
		}	
			
			
		return decls;
	}
			
}
