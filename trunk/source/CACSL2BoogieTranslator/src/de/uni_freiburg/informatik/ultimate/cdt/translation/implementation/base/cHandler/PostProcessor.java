package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionListRec;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.IHandler;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
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
	private HashSet<String> mInitializedGlobals;

	/**
	 * Constructor.
	 */
	public PostProcessor() {
		mInitializedGlobals = new HashSet<String>();
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
	public ArrayList<Declaration> postProcess(Dispatcher main, ILocation loc,
			MemoryHandler memoryHandler, ArrayHandler arrayHandler, FunctionHandler functionHandler, StructHandler structHandler,
			HashMap<String, Procedure> procedures,
			HashMap<String, HashSet<String>> modifiedGlobals,
			Set<String> undefinedTypes,
			Collection<? extends FunctionDeclaration> functions, 
			HashMap<Declaration,CDeclaration> mDeclarationsGlobalInBoogie
			) {
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		decl.addAll(declareUndefinedTypes(loc, undefinedTypes));
		decl.addAll(createUltimateInitProcedure(loc, main, memoryHandler, arrayHandler, functionHandler, structHandler,
				mDeclarationsGlobalInBoogie));
		decl.addAll(createUltimateStartProcedure(main, loc, functionHandler, procedures,
				modifiedGlobals));
		decl.addAll(functions);
		return decl;
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
	 * @param loc
	 *            the location of the translation unit. declaration.
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param memoryHandler 
	 * @param arrayHandler
	 *            a reference to the arrayHandler.
	 * @param structHandler 
	 * @param mDeclarationsGlobalInBoogie 
	 * @param initStatements
	 *            a list of all global init statements.
	 * @param uninitGlobalVars
	 *            a set of uninitialized global variables.
	 * @return a list the initialized variables.
	 */
	private ArrayList<Declaration> createUltimateInitProcedure(ILocation loc,
			Dispatcher main, MemoryHandler memoryHandler, ArrayHandler arrayHandler, FunctionHandler functionHandler,   
			StructHandler structHandler, HashMap<Declaration, CDeclaration> mDeclarationsGlobalInBoogie
//			ArrayList<Statement> initStatements, Collection<String> uninitGlobalVars
			) {
		functionHandler.beginUltimateInit(main, loc, SFO.INIT);
		ArrayList<Statement> initStatements = new ArrayList<Statement>();
		
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<VariableDeclaration> initDecl = new ArrayList<VariableDeclaration>();
		if (main.isMMRequired()) {
			LeftHandSide[] lhs = new LeftHandSide[] { new ArrayLHS(loc,
					new VariableLHS(loc, SFO.VALID),
					new Expression[] { new IntegerLiteral(loc, SFO.NR0) }) };
			Expression[] rhs = new Expression[] { new BooleanLiteral(loc, false) };
			initStatements.add(0, new AssignmentStatement(loc, lhs, rhs));
			mInitializedGlobals.add(SFO.VALID);

			VariableLHS slhs = new VariableLHS(loc, SFO.NULL);
			initStatements.add(0, new AssignmentStatement(loc, 
					new LeftHandSide[] { slhs }, 
					new Expression[] { MemoryHandler.constructNullPointer(loc)}));
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
		for (Entry<Declaration, CDeclaration> en : mDeclarationsGlobalInBoogie.entrySet()) {
			if (en.getKey() instanceof TypeDeclaration)
				continue;
			ResultExpression initializer = en.getValue().getInitializer();
			if (initializer != null) {
				assert ((VariableDeclaration)en.getKey()).getVariables().length == 1 
						&& ((VariableDeclaration)en.getKey()).getVariables()[0].getIdentifiers().length == 1;
				String bId = ((VariableDeclaration)en.getKey()).getVariables()[0].getIdentifiers()[0].toString();
				ResultExpression initRex = 
						PostProcessor.initVar(loc, main, memoryHandler, arrayHandler, functionHandler, structHandler, 
								new VariableLHS(loc, bId), en.getValue().getType(), initializer);
				initStatements.addAll(initRex.stmt);
				for (Declaration d : initRex.decl)
					initDecl.add((VariableDeclaration) d);
			} else { //no initializer --> default initialization
				for (VarList vl  : ((VariableDeclaration) en.getKey()).getVariables()) {
					for (String id : vl.getIdentifiers()) {
						ResultExpression nullInitializer = initVar(loc, main, 
								memoryHandler, arrayHandler, functionHandler, structHandler, 
										new VariableLHS(loc, id), en.getValue().getType(), null) ;
						
						initStatements.addAll(nullInitializer.stmt);
						for (Declaration d : nullInitializer.decl)
							initDecl.add((VariableDeclaration) d);
					}
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
			modifyList[i++] = new VariableLHS(loc, var);
		}
		specsInit[0] = new ModifiesSpecification(loc, false, modifyList);
		Procedure initProcedureDecl = new Procedure(loc, new Attribute[0], SFO.INIT, new String[0],
				new VarList[0], new VarList[0], specsInit, null);
		Body initBody = new Body(loc,//TODO: do we need auxVars here, too??
				initDecl.toArray(new VariableDeclaration[0]),
				initStatements.toArray(new Statement[0]));
		decl.add(new Procedure(loc, new Attribute[0], SFO.INIT, new String[0],
				new VarList[0], new VarList[0], null, initBody));
		
		functionHandler.endUltimateInit(main, initProcedureDecl, SFO.INIT);
		return decl;
	}

	/**
	 * Initializes global variables recursively, according to ISO/IEC 9899:TC3,
	 * 6.7.8 §10:<br>
	 * <blockquote
	 * cite="http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf"><i>"If
	 * an object that has automatic storage duration is not initialized
	 * explicitly, its value is indeterminate. If an object that has static
	 * storage duration is not initialized explicitly, then:
	 * <ul>
	 * <li>if it has pointer type, it is initialized to a null pointer;</li>
	 * <li>if it has arithmetic type, it is initialized to (positive or
	 * unsigned) zero;</li>
	 * <li>if it is an aggregate, every member is initialized (recursively)
	 * according to these rules;</li>
	 * <li>if it is a union, the first named member is initialized (recursively)
	 * according to these rules."</li>
	 * </ul>
	 * </i></blockquote> where (from 6.2.5 Types §21): <blockquote
	 * cite="http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf"
	 * ><i>"Arithmetic types and pointer types are collectively called scalar
	 * types. Array and structure types are collectively called aggregate
	 * types."</i></blockquote>
	 * 
	 * @param loc
	 *            the location of the variables declaration.
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param memoryHandler 
	 * @param arrayHandler
	 *            a reference to the arrayHandler.
	 * @param structHandler 
	 * @param lhs
	 *            the LeftHandSide to initialize.
	 * @param at
	 *            the type of this variable.
	 * @param cvar
	 *            the corresponding C variable description.
	 * 
	 * @return a set of Statements, assigning values to the variables.
	 */
	public static ResultExpression initVar(ILocation loc, Dispatcher main,
			MemoryHandler memoryHandler, ArrayHandler arrayHandler, FunctionHandler functionHandler, 
			StructHandler structHandler, final LeftHandSide lhs,
			CType cvar, ResultExpression initializerRaw) {
		CType lCvar = cvar.getUnderlyingType();
		
		
		//TODO: deal with varsOnHeap
		boolean onHeap = false;
		if (lhs instanceof VariableLHS) 
			onHeap = ((CHandler )main.cHandler).isHeapVar(((VariableLHS) lhs).getIdentifier());
	
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new HashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
		
		//if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
		//carry over
		ResultExpression initializer = null;
		if (initializerRaw != null) {
			initializer = 
					initializerRaw.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			stmt.addAll(initializer.stmt);
			decl.addAll(initializer.decl);
			overappr.addAll(initializer.overappr);
			auxVars.putAll(initializer.auxVars);
		}
		
		ArrayList<Expression> rhs = new ArrayList<Expression>();
		if (lCvar instanceof CPrimitive) {
			switch (((CPrimitive) lCvar).getType()) {
			case BOOL:
			case CHAR:
			case CHAR16:
			case CHAR32:
			case WCHAR:
			case INT:
				if (initializer == null) {
					rhs.add(new IntegerLiteral(loc, SFO.NR0));
				} else {
					rhs.add(initializer.lrVal.getValue());
				}
				break;
			case DOUBLE:
			case FLOAT:
				if (initializer == null) {
					rhs.add(new RealLiteral(loc, SFO.NR0F));
				} else {
					rhs.add(initializer.lrVal.getValue());
				}
			case VOID:
			default:
				throw new AssertionError("unknown type to init");
			}
			stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					rhs.toArray(new Expression[0])));
		} else if (lCvar instanceof CArray) {

			if (onHeap) { 
				String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT);
				VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, MemoryHandler.POINTER_TYPE, loc);

				ResultExpression mallocRex = memoryHandler.getMallocCall(
						main, functionHandler, memoryHandler.calculateSizeOf(lCvar, loc), new LocalLValue(new VariableLHS(loc, tmpId), lCvar), loc);
				stmt.addAll(mallocRex.stmt);
				decl.addAll(mallocRex.decl);
				auxVars.putAll(mallocRex.auxVars);
				overappr.addAll(mallocRex.overappr);

				Statement assign = new AssignmentStatement(loc, new LeftHandSide[] {lhs}, new Expression[] { mallocRex.lrVal.getValue()});

				stmt.add(assign);
				decl.add(tVarDecl);
				auxVars.put(tVarDecl, loc);

				stmt.addAll(arrayHandler.initArrayOnHeap(main, memoryHandler, structHandler, loc, 
						initializer == null ? null : ((ResultExpressionListRec) initializer).list,
						CHandler.convertLHSToExpression(lhs), functionHandler, (CArray) lCvar));
			} else { //not on Heap
				stmt.addAll(arrayHandler.initBoogieArray(main, memoryHandler, structHandler, functionHandler, loc,
						initializer == null ? null : ((ResultExpressionListRec) initializer).list,
						lhs, (CArray) lCvar));
			}
		} else if (lCvar instanceof CStruct) {
			
			CStruct structType = (CStruct) lCvar;
			//			for (VarList vl : ((StructType) at).getFields()) {
			ResultExpression scRex = structHandler.makeStructConstructorFromRERL(main, 
					loc, memoryHandler, arrayHandler, functionHandler, 
					(ResultExpressionListRec) initializer,
					structType, onHeap);
			
			stmt.addAll(scRex.stmt);
			decl.addAll(scRex.decl);
			overappr.addAll(scRex.overappr);
			auxVars.putAll(scRex.auxVars);
			stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { scRex.lrVal.getValue() }));
		} else if (lCvar instanceof CPointer) {
			LRValue nullPointer = new RValue(new IdentifierExpression(loc, SFO.NULL), 
					null);
			stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { nullPointer.getValue() } ));
		} else {
			String msg = "Unknown type - don't know how to initialize!";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		assert (main.isAuxVarMapcomplete(decl, auxVars));

		// LRValue is null because it is not needed, we need only the statement(s) and declaration(s)
		return new ResultExpression(stmt, null, decl, auxVars, overappr);
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
			Dispatcher main, ILocation loc, FunctionHandler functionHandler,
			HashMap<String, Procedure> procedures,
			HashMap<String, HashSet<String>> modifiedGlobals) {
		functionHandler.beginUltimateInit(main, loc, SFO.START);
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		String checkMethod = main.getCheckedMethod();
		
		Procedure startDeclaration = null;
		Specification[] specsStart = new Specification[0];
		
		if (functionHandler.getCallGraph().containsKey(SFO.START))
				functionHandler.getCallGraph().put(SFO.START, new HashSet<String>());
		functionHandler.getCallGraph().get(SFO.START).add(SFO.INIT);
		
		if (!checkMethod.equals(SFO.EMPTY)
				&& procedures.containsKey(checkMethod)) {
			IHandler.s_Logger.info("Settings: Checked method=" + checkMethod);

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
				// CHandler.getTempVarVariableDeclaration(checkMethodRet,
				// out[0].getType()., loc);
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
			HashSet<VariableLHS> startModifiesClause = new HashSet<VariableLHS>();
			for (String id: mInitializedGlobals)
				startModifiesClause.add(new VariableLHS(loc, id));
			for (String id: modifiedGlobals.get(checkMethod))
				startModifiesClause.add(new VariableLHS(loc, id));
			specsStart[0] = new ModifiesSpecification(loc, false,
					startModifiesClause.toArray(new VariableLHS[0]));

//			decl.add(startDecl);
			Body startBody = new Body(loc,
					startDecl.toArray(new VariableDeclaration[0]),
					startStmt.toArray(new Statement[0]));
			decl.add(new Procedure(loc, new Attribute[0], SFO.START,
					new String[0], new VarList[0], new VarList[0], null,
					startBody));

		} else if (!checkMethod.equals(SFO.EMPTY)
				&& !procedures.containsKey(checkMethod)) {
			String msg = "You specified the starting procedure: "
					+ checkMethod
					+ "\n The program does not have this method. ULTIMATE will continue in library mode (i.e., each procedure can be starting procedure and global variables are not initialized).";
			Dispatcher.warn(loc, msg);
		} else {
			IHandler.s_Logger.info("Settings: Library mode!");
			if (procedures.containsKey("main")) {
				String msg = "You selected the library mode (i.e., each procedure can be starting procedure and global variables are not initialized). This program contains a \"main\" procedure. Maybe you wanted to select the \"main\" procedure as starting procedure.";
				Dispatcher.warn(loc, msg);
			}
		}
		startDeclaration = new Procedure(loc, new Attribute[0], SFO.START,
				new String[0], new VarList[0], new VarList[0], specsStart,
				null);
		functionHandler.endUltimateInit(main, startDeclaration, SFO.START);
		return decl;
	}
}
