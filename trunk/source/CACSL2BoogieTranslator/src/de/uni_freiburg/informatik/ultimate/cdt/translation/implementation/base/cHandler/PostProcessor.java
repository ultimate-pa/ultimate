package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.internal.core.dom.parser.c.CPointerType;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.IHandler;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * Class caring for some post processing steps, like creating an initializer
 * procedure and the start procedure.
 * 
 * @author Markus Lindenmann
 * @date 12.10.2012
 */
public class PostProcessor {
	/**
	 * Holds the Boogie identifiers of the initialized global variables.
	 */
	private HashSet<String> initializedGlobals;

	/**
	 * Constructor.
	 */
	public PostProcessor() {
		initializedGlobals = new HashSet<String>();
	}

	/**
	 * Start method for the post processing.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param loc
	 *            the location of the translation unit.
	 * @param arrayHandler
	 *            a reference to the arrayHandler.
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
	 * @param uninitGlobalVars
	 *            a set of uninitialized global variables.
	 * @return a declaration list holding the init() and start() procedure.
	 */
	public ArrayList<Declaration> postProcess(Dispatcher main, ILocation loc,
			ArrayHandler arrayHandler, ArrayList<Statement> initStatements,
			HashMap<String, Procedure> procedures,
			HashMap<String, HashSet<String>> modifiedGlobals,
			Set<String> undefinedTypes,
			Collection<? extends FunctionDeclaration> functions,
			Collection<String> uninitGlobalVars) {
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		decl.addAll(declareUndefinedTypes(loc, undefinedTypes));
		decl.addAll(createUltimateInitProcedure(loc, main, arrayHandler,
				initStatements, uninitGlobalVars));
		decl.addAll(createUltimateStartProcedure(main, loc, procedures,
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
	 * @param arrayHandler
	 *            a reference to the arrayHandler.
	 * @param initStatements
	 *            a list of all global init statements.
	 * @param uninitGlobalVars
	 *            a set of uninitialized global variables.
	 * @return a list the initialized variables.
	 */
	private ArrayList<Declaration> createUltimateInitProcedure(ILocation loc,
			Dispatcher main, ArrayHandler arrayHandler,
			ArrayList<Statement> initStatements,
			Collection<String> uninitGlobalVars) {
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<VariableDeclaration> initDecl = new ArrayList<VariableDeclaration>();
		for (Statement stmt : initStatements) {
			if (stmt instanceof AssignmentStatement) {
				AssignmentStatement ass = (AssignmentStatement) stmt;
				assert ass.getLhs().length == 1; // by construction ...
				LeftHandSide lhs = ass.getLhs()[0];
				String id = BoogieASTUtil.getLHSId(lhs);
				initializedGlobals.add(id);
			}
		}
		for (String bId : uninitGlobalVars) {
			assert main.cHandler.getSymbolTable().containsBoogieSymbol(bId);
			String cId = main.cHandler.getSymbolTable().getCID4BoogieID(bId,
					loc);
			assert main.cHandler.getSymbolTable().containsCSymbol(cId);
			CACSLLocation lloc = (CACSLLocation) main.cHandler.getSymbolTable()
					.get(cId, loc).getDecl().getLocation();
			ASTType at = main.cHandler.getSymbolTable().getTypeOfVariable(cId,
					lloc);
			CType cvar = main.cHandler.getSymbolTable().get(cId, lloc)
					.getCVariable();
			LeftHandSide lhs = new VariableLHS(lloc, new InferredType(at), bId);
			ResultExpression r = initVar(lloc, main, arrayHandler, lhs, at,
					cvar);
			initStatements.addAll(0, r.stmt);
			for (Declaration d : r.decl) {
				assert d instanceof VariableDeclaration;
				initDecl.add((VariableDeclaration) d);
			}
		}
		if (main.isMMRequired()) {
			LeftHandSide[] lhs = new LeftHandSide[] { new ArrayLHS(loc,
					new VariableLHS(loc, SFO.VALID),
					new Expression[] { new IntegerLiteral(loc, SFO.NR0) }) };
			Expression[] rhs = new Expression[] { new BooleanLiteral(loc, false) };
			initStatements.add(new AssignmentStatement(loc, lhs, rhs));
			initializedGlobals.add(SFO.VALID);

			VariableLHS slhs = new VariableLHS(loc, SFO.NULL);
			LeftHandSide[] lhsNullB = new LeftHandSide[] { new StructLHS(loc,
					slhs, SFO.POINTER_BASE) };
			// LeftHandSide[] lhsNullO = new LeftHandSide[]{
			// new StructLHS(loc, slhs, SFO.POINTER_OFFSET)
			// };
			Expression[] rhsNull = new Expression[] { new IntegerLiteral(loc,
					SFO.NR0) };
			initStatements.add(new AssignmentStatement(loc, lhsNullB, rhsNull));
			// initStatements.add(new AssignmentStatement(loc, lhsNullO,
			// rhsNull));
			initializedGlobals.add(SFO.NULL);
		}
		initializedGlobals.addAll(uninitGlobalVars);
		Specification[] specsInit = new Specification[1];
		specsInit[0] = new ModifiesSpecification(loc, false,
				initializedGlobals.toArray(new String[0]));
		decl.add(new Procedure(loc, new Attribute[0], SFO.INIT, new String[0],
				new VarList[0], new VarList[0], specsInit, null));
		Body initBody = new Body(loc,
				initDecl.toArray(new VariableDeclaration[0]),
				initStatements.toArray(new Statement[0]));
		decl.add(new Procedure(loc, new Attribute[0], SFO.INIT, new String[0],
				new VarList[0], new VarList[0], null, initBody));
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
	 * @param arrayHandler
	 *            a reference to the arrayHandler.
	 * @param lhs
	 *            the LeftHandSide to initialize.
	 * @param at
	 *            the type of this variable.
	 * @param cvar
	 *            the corresponding C variable description.
	 * 
	 * @return a set of Statements, assigning values to the variables.
	 */
	private ResultExpression initVar(final CACSLLocation loc, Dispatcher main,
			final ArrayHandler arrayHandler, final LeftHandSide lhs,
			final ASTType at, CType cvar) {
		CType lCvar = cvar;
		if (cvar instanceof CNamed) {
			lCvar = ((CNamed) cvar).getUnderlyingType();
		}
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
		if (at instanceof PrimitiveType) {
			InferredType it = new InferredType(at);
			InferredType.Type t = it.getType();
			ArrayList<Expression> rhs = new ArrayList<Expression>();
			switch (t) {
			case Boolean:
				rhs.add(new BooleanLiteral(loc, it, false));
				break;
			case Integer:
				rhs.add(new IntegerLiteral(loc, it, SFO.NR0));
				break;
			case Real:
				rhs.add(new RealLiteral(loc, it, SFO.NR0F));
				break;
			default:
				throw new AssertionError("There are no Strings in Boogie ...");

			}
			stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					rhs.toArray(new Expression[0])));
		} else if (at instanceof ArrayType) {
			assert lCvar instanceof CArray;
			ArrayList<IdentifierExpression> tempIdc = new ArrayList<IdentifierExpression>();
			Expression[] arrSize = ((CArray) lCvar).getDimensions();
			Expression nr0 = new IntegerLiteral(loc, SFO.NR0);
			for (int i = 0; i < arrSize.length; i++) {
				String tempVarName = main.nameHandler
						.getTempVarUID(SFO.AUXVAR.ARRAYINIT);
				InferredType tempVarIType = new InferredType(Type.Integer);
				tempIdc.add(new IdentifierExpression(loc, tempVarIType,
						tempVarName));
				VariableDeclaration tVarDecl = SFO
						.getTempVarVariableDeclaration(tempVarName,
								tempVarIType, loc);
				auxVars.put(tVarDecl, loc);
				decl.add(tVarDecl);
				if (i == 0) {
					stmt.add(new AssignmentStatement(loc,
							new LeftHandSide[] { new VariableLHS(loc,
									tempVarName) }, new Expression[] { nr0 }));
				}
			}
			assert arrSize.length == tempIdc.size();
			ArrayList<Statement> whileBody = new ArrayList<Statement>();
			ArrayLHS arrLhs = new ArrayLHS(loc, new InferredType(at), lhs,
					tempIdc.toArray(new Expression[0]));
			ResultExpression r = initVar(loc, main, arrayHandler, arrLhs,
					((ArrayType) at).getValueType(),
					((CArray) lCvar).getValueType());
			decl.addAll(r.decl);
			auxVars.putAll(r.auxVars);
			WhileStatement ws = null;
			Expression nr1 = new IntegerLiteral(loc, SFO.NR1);
			for (int i = arrSize.length - 1; i >= 0; i--) {
				if (i == arrSize.length - 1) {
					whileBody.addAll(r.stmt);
				} else {
					VariableLHS tmpLhsNext = new VariableLHS(loc, tempIdc.get(
							i + 1).getIdentifier());
					whileBody.add(new AssignmentStatement(loc,
							new LeftHandSide[] { tmpLhsNext },
							new Expression[] { nr0 }));
					whileBody.add(ws);
				}
				VariableLHS tmpLhs = new VariableLHS(loc, tempIdc.get(i)
						.getIdentifier());
				whileBody.add(new AssignmentStatement(loc,
						new LeftHandSide[] { tmpLhs },
						new Expression[] { new BinaryExpression(loc,
								new InferredType(Type.Integer),
								Operator.ARITHPLUS, tempIdc.get(i), nr1) }));
				ws = new WhileStatement(loc, new BinaryExpression(loc,
						new InferredType(Type.Integer),
						BinaryExpression.Operator.COMPLT, tempIdc.get(i),
						arrSize[i]), new LoopInvariantSpecification[0],
						whileBody.toArray(new Statement[0]));
				whileBody.clear();

			}
			stmt.add(ws);
		} else if (at instanceof StructType) {
			assert lCvar instanceof CStruct;
			for (VarList vl : ((StructType) at).getFields()) {
				for (String id : vl.getIdentifiers()) {
					ResultExpression r = initVar(loc, main, arrayHandler,
							new StructLHS(loc, lhs, id), vl.getType(),
							((CStruct) lCvar).getFieldType(id));
					decl.addAll(r.decl);
					stmt.addAll(r.stmt);
					auxVars.putAll(r.auxVars);
				}
			}
		} else if ((at instanceof NamedType) && 
				((NamedType) at).getName().equals(SFO.POINTER)){
			assert lCvar instanceof CPointer;
			//result is pointer to 0
			Expression nullPointer = new IdentifierExpression(loc, at.getBoogieType(), SFO.NULL);
			return new ResultExpression(nullPointer, auxVars);
		}
		else {
			String msg = "Unknown type - don't know how to initialize!";
			Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
			throw new UnsupportedSyntaxException(msg);
		}
		assert (main.isAuxVarMapcomplete(decl, auxVars));
		return new ResultExpression(stmt, null, decl, auxVars);
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
			Dispatcher main, ILocation loc,
			HashMap<String, Procedure> procedures,
			HashMap<String, HashSet<String>> modifiedGlobals) {
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		String checkMethod = main.getCheckedMethod();
		if (!checkMethod.equals(SFO.EMPTY)
				&& procedures.containsKey(checkMethod)) {
			IHandler.s_Logger.info("Settings: Checked method=" + checkMethod);
			ArrayList<Statement> startStmt = new ArrayList<Statement>();
			ArrayList<VariableDeclaration> startDecl = new ArrayList<VariableDeclaration>();
			Specification[] specsStart = new Specification[1];
			startStmt.add(new CallStatement(loc, false, new String[0],
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
						new String[] { checkMethodRet }, checkMethod, args
								.toArray(new Expression[0])));
			} else { // void
				startStmt.add(new CallStatement(loc, false, new String[0],
						checkMethod, args.toArray(new Expression[0])));
			}
			HashSet<String> startModifiesClause = new HashSet<String>();
			startModifiesClause.addAll(initializedGlobals);
			startModifiesClause.addAll(modifiedGlobals.get(checkMethod));
			specsStart[0] = new ModifiesSpecification(loc, false,
					startModifiesClause.toArray(new String[0]));
			decl.add(new Procedure(loc, new Attribute[0], SFO.START,
					new String[0], new VarList[0], new VarList[0], specsStart,
					null));
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
			Dispatcher.warn(loc, "Starting procedure not found", msg);
		} else {
			IHandler.s_Logger.info("Settings: Library mode!");
			if (procedures.containsKey("main")) {
				String msg = "You selected the library mode (i.e., each procedure can be starting procedure and global variables are not initialized). This program contains a \"main\" procedure. Maybe you wanted to select the \"main\" procedure as starting procedure.";
				Dispatcher.warn(loc, "Program has main procedure", msg);
			}
		}
		return decl;
	}
}
