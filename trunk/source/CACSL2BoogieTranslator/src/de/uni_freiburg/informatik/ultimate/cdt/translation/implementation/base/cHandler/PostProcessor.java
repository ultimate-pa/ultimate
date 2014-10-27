package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

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
	private final Logger mLogger;

	/**
	 * Constructor.
	 */
	public PostProcessor(Dispatcher dispatcher, Logger logger) {
		mInitializedGlobals = new LinkedHashSet<String>();
		mDispatcher = dispatcher;
		mLogger = logger;
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
	 * @param uninitGlobalVars
	 *            a set of uninitialized global variables.
	 * @return a declaration list holding the init() and start() procedure.
	 */
	public ArrayList<Declaration> postProcess(Dispatcher main, ILocation loc, MemoryHandler memoryHandler, 
			ArrayHandler arrayHandler, FunctionHandler functionHandler, StructHandler structHandler,
			Set<String> undefinedTypes,	Collection<? extends FunctionDeclaration> functions, 
			LinkedHashMap<Declaration,CDeclaration> mDeclarationsGlobalInBoogie) {
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		decl.addAll(declareUndefinedTypes(loc, undefinedTypes));
		decl.addAll(createUltimateInitProcedure(loc, main, memoryHandler, arrayHandler, functionHandler, structHandler,
				mDeclarationsGlobalInBoogie));
		decl.addAll(createUltimateStartProcedure(main, loc, functionHandler));
		decl.addAll(functions);
		decl.addAll(declareFunctionPointerProcedures(main, functionHandler, memoryHandler, structHandler));
		decl.addAll(declareConversionFunctions(main, functionHandler, memoryHandler, structHandler));
		return decl;
	}
	
	private ArrayList<Declaration> declareConversionFunctions(
			Dispatcher main, FunctionHandler functionHandler, 
			MemoryHandler memoryHandler, StructHandler structHandler) {

		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		ArrayList<Declaration> decls = new ArrayList<>();
		
		
		// function to_int
		String inReal = "inReal";
//		IdentifierExpression inRealIdex = new IdentifierExpression(ignoreLoc, inReal);
		String outInt = "outInt";
//		IdentifierExpression outIntIdex = new IdentifierExpression(ignoreLoc, outInt);
		VarList realParam = new VarList(ignoreLoc, new String[] {  }, new PrimitiveType(ignoreLoc, SFO.REAL));
		VarList[] oneRealParam = new VarList[] { realParam };
		VarList intParam = new VarList(ignoreLoc, new String[] { outInt }, new PrimitiveType(ignoreLoc, SFO.INT));
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

		decls.add(new FunctionDeclaration(ignoreLoc, new Attribute[0], SFO.TO_INT, new String[0], oneRealParam, intParam));

		return decls;
	}

	private ArrayList<Declaration> declareFunctionPointerProcedures(
			Dispatcher main, FunctionHandler functionHandler, 
			MemoryHandler memoryHandler, StructHandler structHandler) {
		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		ArrayList<Declaration> result = new ArrayList<>();
		for (CFunction cFunc : functionHandler.functionSignaturesThatHaveAFunctionPointer) {
			String procName = cFunc.functionSignatureAsProcedureName();
			

			VarList[] inParams = functionHandler.getProcedures().get(procName).getInParams();
			VarList[] outParams = functionHandler.getProcedures().get(procName).getOutParams();
			assert outParams.length <= 1;
			Procedure functionPointerMuxProc = new Procedure(ignoreLoc, new Attribute[0], 
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
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		for (String s : undefinedTypes) {
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
			StructHandler structHandler, LinkedHashMap<Declaration, CDeclaration> declarationsGlobalInBoogie) {
		functionHandler.beginUltimateInit(main, translationUnitLoc, SFO.INIT);
		ArrayList<Statement> initStatements = new ArrayList<Statement>();

		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<VariableDeclaration> initDecl = new ArrayList<VariableDeclaration>();
		if (main.isMMRequired()) {
			if (memoryHandler.isFloatArrayRequiredInMM ||
					memoryHandler.isIntArrayRequiredInMM ||
					memoryHandler.isPointerArrayRequiredInMM) {
				LeftHandSide[] lhs = new LeftHandSide[] { new ArrayLHS(translationUnitLoc,
						new VariableLHS(translationUnitLoc, SFO.VALID),
						new Expression[] { new IntegerLiteral(translationUnitLoc, SFO.NR0) }) };
				Expression[] rhs = new Expression[] { new BooleanLiteral(translationUnitLoc, false) };
				initStatements.add(0, new AssignmentStatement(translationUnitLoc, lhs, rhs));
				mInitializedGlobals.add(SFO.VALID);
			}

			VariableLHS slhs = new VariableLHS(translationUnitLoc, SFO.NULL);
			initStatements.add(0, new AssignmentStatement(translationUnitLoc, 
					new LeftHandSide[] { slhs }, 
					new Expression[] { new StructConstructor(translationUnitLoc, new String[]{"base", "offset"}, 
							new Expression[]{new IntegerLiteral(translationUnitLoc, "0"), new IntegerLiteral(translationUnitLoc, "0")})}));
			mInitializedGlobals.add(SFO.NULL);
		}
		for (Statement stmt : initStatements) {
			if (stmt instanceof AssignmentStatement) {
				AssignmentStatement ass = (AssignmentStatement) stmt;
				assert ass.getLhs().length == 1; // by construction ...
				LeftHandSide lhs = ass.getLhs()[0];
				String id = BoogieASTUtil.getLHSId(lhs);
				mInitializedGlobals.add(id);
			}
		}

		//initialization for statics and other globals
		for (Entry<Declaration, CDeclaration> en : declarationsGlobalInBoogie.entrySet()) {
			if (en.getKey() instanceof TypeDeclaration || en.getKey() instanceof ConstDeclaration)
				continue;
			ILocation currentDeclsLoc = en.getKey().getLocation();
			ResultExpression initializer = en.getValue().getInitializer();

			for (VarList vl  : ((VariableDeclaration) en.getKey()).getVariables()) {
				for (String id : vl.getIdentifiers()) {
					if (main.cHandler.isHeapVar(id)) {
						initStatements.add(memoryHandler.getMallocCall(main, functionHandler, 
								memoryHandler.calculateSizeOf(en.getValue().getType(), currentDeclsLoc), 
								new LocalLValue(new VariableLHS(currentDeclsLoc, id), en.getValue().getType()), currentDeclsLoc));
					}

					//					if (initializer != null) {
					//						assert ((VariableDeclaration)en.getKey()).getVariables().length == 1 
					//								&& ((VariableDeclaration)en.getKey()).getVariables()[0].getIdentifiers().length == 1;
					ResultExpression initRex = 
							main.cHandler.getInitHandler().initVar(currentDeclsLoc, main, 
									new VariableLHS(currentDeclsLoc, id), en.getValue().getType(), initializer);
					initStatements.addAll(initRex.stmt);
					initStatements.addAll(CHandler.createHavocsForNonMallocAuxVars(initRex.auxVars));
					for (Declaration d : initRex.decl)
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
			for (VarList vl  : ((VariableDeclaration) en.getKey()).getVariables())
				mInitializedGlobals.addAll(Arrays.asList(vl.getIdentifiers()));
		}

		mInitializedGlobals.addAll(functionHandler.getModifiedGlobals().get(SFO.INIT));

		Specification[] specsInit = new Specification[1];

		VariableLHS[] modifyList = new VariableLHS[mInitializedGlobals.size()];
		int i = 0;
		for (String var: mInitializedGlobals) {
			modifyList[i++] = new VariableLHS(translationUnitLoc, var);
		}
		specsInit[0] = new ModifiesSpecification(translationUnitLoc, false, modifyList);
		Procedure initProcedureDecl = new Procedure(translationUnitLoc, new Attribute[0], SFO.INIT, new String[0],
				new VarList[0], new VarList[0], specsInit, null);
		Body initBody = new Body(translationUnitLoc,
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
		LinkedHashMap<String, Procedure> procedures = functionHandler.getProcedures();
		LinkedHashMap<String, LinkedHashSet<String>> modifiedGlobals = functionHandler.getModifiedGlobals();

		functionHandler.beginUltimateInit(main, loc, SFO.START);
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		String checkMethod = main.getCheckedMethod();

		Procedure startDeclaration = null;
		Specification[] specsStart = new Specification[0];

		if (functionHandler.getCallGraph().containsKey(SFO.START))
			functionHandler.getCallGraph().put(SFO.START, new LinkedHashSet<String>());
		functionHandler.getCallGraph().get(SFO.START).add(SFO.INIT);

		if (!checkMethod.equals(SFO.EMPTY)
				&& procedures.containsKey(checkMethod)) {
			mLogger.info("Settings: Checked method=" + checkMethod);

			functionHandler.getCallGraph().get(SFO.START).add(checkMethod);

			ArrayList<Statement> startStmt = new ArrayList<Statement>();
			ArrayList<VariableDeclaration> startDecl = new ArrayList<VariableDeclaration>();
			specsStart = new Specification[1];
			startStmt.add(new CallStatement(loc, false, new VariableLHS[0],
					SFO.INIT, new Expression[0]));
			VarList[] out = procedures.get(checkMethod).getOutParams();
			VarList[] in = procedures.get(checkMethod).getInParams();
			ArrayList<Expression> args = new ArrayList<Expression>();
			if (in.length > 0) {
				startDecl
				.add(new VariableDeclaration(loc, new Attribute[0], in));
				for (VarList arg : in) {
					assert arg.getIdentifiers().length == 1; // by construction
					String id = arg.getIdentifiers()[0];
					args.add(new IdentifierExpression(loc, id));
				}
			}
			if (out.length != 0) {
				assert out.length == 1;
				// there is 1(!) return value
				String checkMethodRet = main.nameHandler
						.getTempVarUID(SFO.AUXVAR.RETURNED);
				main.cHandler.getSymbolTable().addToReverseMap(checkMethodRet,
						SFO.NO_REAL_C_VAR + checkMethodRet, loc);
				VarList tempVar = new VarList(loc,
						new String[] { checkMethodRet }, out[0].getType());
				VariableDeclaration tmpVar = new VariableDeclaration(loc,
						new Attribute[0], new VarList[] { tempVar });
				startDecl.add(tmpVar);
				startStmt.add(new CallStatement(loc, false,
						new VariableLHS[] { new VariableLHS(loc, checkMethodRet) }, 
						checkMethod, args.toArray(new Expression[0])));
			} else { // void
				startStmt.add(new CallStatement(loc, false, new VariableLHS[0],
						checkMethod, args.toArray(new Expression[0])));
			}
			LinkedHashSet<VariableLHS> startModifiesClause = new LinkedHashSet<VariableLHS>();
			for (String id: mInitializedGlobals)
				startModifiesClause.add(new VariableLHS(loc, id));
			//			if (mSomethingOnHeapIsInitialized) {
			//				for (String t : new String[] { SFO.INT, SFO.POINTER,
			//						SFO.REAL/*, SFO.BOOL */}) {
			//					startModifiesClause.add(new VariableLHS(loc, SFO.MEMORY + "_" + t));
			//				}		
			//			}
			for (String id: modifiedGlobals.get(checkMethod))
				startModifiesClause.add(new VariableLHS(loc, id));
			specsStart[0] = new ModifiesSpecification(loc, false,
					startModifiesClause.toArray(new VariableLHS[0]));

			Body startBody = new Body(loc,
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
		} else {
			mLogger.info("Settings: Library mode!");
			if (procedures.containsKey("main")) {
				String msg = "You selected the library mode (i.e., each procedure can be starting procedure and global variables are not initialized). This program contains a \"main\" procedure. Maybe you wanted to select the \"main\" procedure as starting procedure.";
				mDispatcher.warn(loc, msg);
			}
		}
		startDeclaration = new Procedure(loc, new Attribute[0], SFO.START,
				new String[0], new VarList[0], new VarList[0], specsStart,
				null);
		functionHandler.endUltimateInit(main, startDeclaration, SFO.START);
		return decl;
	}
}
