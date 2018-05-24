/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jeremi Dzienian
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE Cookiefy plug-in.
 *
 * The ULTIMATE Cookiefy plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Cookiefy plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Cookiefy plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Cookiefy plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Cookiefy plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.cookiefy.ContextPath.ContextPathAlphaNode;
import de.uni_freiburg.informatik.ultimate.cookiefy.ContextPath.ContextPathNode;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Stores the templates for the Boogiepl code inserted by cookiefy.
 *
 * procedure format enc_id_K(locals..., globals..., stack: stack, pp:int)
 *
 * @author Vincent
 * @author Jeremi
 */
public class TemplateStore {

	protected final ILogger mLogger;

	/**
	 * VarList is the array of global state vars.
	 */
	private VarList[] mGlobalStateVars;

	public VarList[] getGlobalStateVars() {
		return mGlobalStateVars;
	}

	// this has to be refactored !!!!
	private int mIntStackFrameCounter = 0;
	private int mBoolStackFrameCounter = 0;

	// ?
	private final IdentMap mIdentMap = new IdentMap();

	/**
	 * AST Prototype for the type definition of the int stack.
	 *
	 * <code>
	 * type iStack = [int][int]int;
	 * </code>
	 */
	public TypeDeclaration mIStackType =
			new TypeDeclaration(LocationProvider.getLocation(), new Attribute[] {}, false, "iStack", new String[] {},
					new ArrayType(LocationProvider.getLocation(), new String[] {},
							new ASTType[] { new PrimitiveType(LocationProvider.getLocation(), "int") },
							new ArrayType(LocationProvider.getLocation(), new String[] {},
									new ASTType[] { new PrimitiveType(LocationProvider.getLocation(), "int") },
									new PrimitiveType(LocationProvider.getLocation(), "int"))));

	/**
	 * AST Prototype for the type definition of the bool stack.
	 *
	 * <code>
	 * type bStack = [int][int]bool;
	 * </code>
	 */
	public TypeDeclaration mBStackType =
			new TypeDeclaration(LocationProvider.getLocation(), new Attribute[] {}, false, "bStack", new String[] {},
					new ArrayType(LocationProvider.getLocation(), new String[] {},
							new ASTType[] { new PrimitiveType(LocationProvider.getLocation(), "int") },
							new ArrayType(LocationProvider.getLocation(), new String[] {},
									new ASTType[] { new PrimitiveType(LocationProvider.getLocation(), "int") },
									new PrimitiveType(LocationProvider.getLocation(), "bool"))));

	/**
	 * AST Prototype for the type definition of the integer array.
	 *
	 * <code>
	 * type iArray = [int]int;
	 * </code>
	 */
	public TypeDeclaration mIArrayType =
			new TypeDeclaration(LocationProvider.getLocation(), new Attribute[] {}, false, "iArray", new String[] {},
					new ArrayType(LocationProvider.getLocation(), new String[] {},
							new ASTType[] { new PrimitiveType(LocationProvider.getLocation(), "int") },
							new PrimitiveType(LocationProvider.getLocation(), "int")));

	/**
	 * AST Prototype for the type definition of the stacks.
	 *
	 * <code>
	 * var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
	 * </code>
	 */
	private final VariableDeclaration mStack =
			new VariableDeclaration(LocationProvider.getLocation(), new Attribute[] {},
					new VarList[] {
							new VarList(LocationProvider.getLocation(), new String[] { "intStack" },
									new NamedType(LocationProvider.getLocation(), "iStack", new ASTType[] {})),
							new VarList(LocationProvider.getLocation(), new String[] { "boolStack" },
									new NamedType(LocationProvider.getLocation(), "bStack", new ASTType[] {})),
							new VarList(LocationProvider.getLocation(), new String[] { "idStack" },
									new NamedType(LocationProvider.getLocation(), "iArray", new ASTType[] {})),
							new VarList(LocationProvider.getLocation(), new String[] { "ppStack" },
									new NamedType(LocationProvider.getLocation(), "iArray", new ASTType[] {})),
							new VarList(LocationProvider.getLocation(), new String[] { "sp" },
									new PrimitiveType(LocationProvider.getLocation(), "int")) });

	/**
	 * AST Prototype for the type definition of the stacks.
	 *
	 * <code>
	 * pp:int
	 * </code>
	 */
	private final VarList mPPVar = new VarList(LocationProvider.getLocation(), new String[] { "pp" },
			new PrimitiveType(LocationProvider.getLocation(), "int"));

	/**
	 * Prefix for cookiefy generated procedure arguments
	 */
	private final String mParameterToVariablePrefix = "cookiefy_args_";

	private final Program mInputProgram;

	public Program getInputProgram() {
		return mInputProgram;
	}

	/**
	 * initializes a new template store for the given unit
	 *
	 * @param u
	 *            unit generated for
	 */
	public TemplateStore(final Program program, final ILogger logger) {
		mLogger = logger;
		mInputProgram = program;
		setGlobalStateVars();
	}

	/**
	 * Generates code for the given temporal formula fragment.
	 *
	 * @see "Cookiefy" Alogrihtm 9
	 * @param cp
	 *            context path
	 * @param p
	 *            procedure the template is generated for
	 * @param pp
	 *            program point
	 * @return AST fragment
	 */
	public Statement[] programFragmentTemplate(final ContextPathNode cp, final Procedure p, final int pp) {
		switch (cp.getFormulaType()) {
		case Alpha:
			final Expression expr = ((ContextPathAlphaNode) cp).getExpression();
			return atomicPropositionTemplate(expr);
		case And:
			return andTemplate(cp.getPath(), p, pp);
		case Or:
			return orTemplate(cp.getPath(), p, pp);
		case AG:
			return constructAGTemplate(cp.getPath(), p, pp, pp);
		case AW:
			return constructAWTemplate(cp.getPath(), p, pp, pp);
		default:
			mLogger.error("No template found for this property operator!");
			return new Statement[0];
		}
	}

	/**
	 * Generates the code for an AND case
	 *
	 * @param contextPath
	 *            the current context path of the encoding
	 * @param p
	 *            the procedure that is currently encoded
	 * @param currentLine
	 *            current line of the code that the template is corresponding to
	 * @return the code for an and in Cooks algorithm
	 * @see programFragmentTemplate <code>
	 * 	 * if (*)
	 * {
	 * 	call ret:= enc_id_kontextpathL(s,...,stack,pp);
	 * } else {
	 * 	call ret:= enc_id_kontextpathR(s,...,stack,pp);
	 * }
	 * </code>
	 */
	private Statement[] andTemplate(final String contextPath, final Procedure p, final int currentLine) {
		final VariableLHS[] ret = new VariableLHS[] { new VariableLHS(LocationProvider.getLocation(), "ret") };
		// left branch call
		final Statement[] lcallL = new Statement[] { new CallStatement(LocationProvider.getLocation(), false, ret,
				methodeNameGen(p, contextPath, "L"), this.concatToEncArgs(p)) };
		// right branch call
		final Statement[] lcallR = new Statement[] { new CallStatement(LocationProvider.getLocation(), false, ret,
				methodeNameGen(p, contextPath, "R"), this.concatToEncArgs(p)) };

		final Statement[] andAST = new Statement[] { new IfStatement(LocationProvider.getLocation(),
				new WildcardExpression(LocationProvider.getLocation()), lcallL, lcallR) };

		return andAST;
	}

	/**
	 * Generates the code for an OR case
	 *
	 * @param contextPath
	 *            the current context path of the encoding
	 * @param p
	 *            the procedure that is currently encoded
	 * @param currentLine
	 *            current line of the code that the template is corresponding to
	 * @return the code for an OR in Cooks algorithm
	 * @see programFragmentTemplate <code>
	 * call ret:= enc_id_kontextpathL(s,...,stack,pp);
	 * if (ret)
	 * {
	 * 	return;
	 * } else {
	 * 	call ret:= enc_id_kontextpathR(s,...,stack,pp);
	 * 	return;
	 * }
	 * </code>
	 */
	private Statement[] orTemplate(final String contextPath, final Procedure p, final int currentLine) {
		final Statement[] orAST = new Statement[2];
		// left call first
		orAST[0] = this.lcall(contextPath, p, currentLine, "L");
		// right call
		final Statement[] lcallR = new Statement[] { this.lcall(contextPath, p, currentLine, "R"),
				new ReturnStatement(LocationProvider.getLocation()) };
		// if left then right
		orAST[1] = new IfStatement(LocationProvider.getLocation(),
				new IdentifierExpression(LocationProvider.getLocation(), "ret"),
				new Statement[] { new ReturnStatement(LocationProvider.getLocation()) }, lcallR);

		return orAST;
	}

	/**
	 * Generates the code for an AG case
	 *
	 * @param contextPath
	 * @param p
	 * @param currentLine
	 * @return the code for an AG in Cooks algorithm
	 * @see programFragmentTemplate
	 *
	 *      <code>
	 * if (*) {ret:= true; return;}
	 * call ret:= encKL(S, pp);
	 * if (!ret){
	 * 	ret:= false; return;
	 * }
	 * </code>
	 */
	private Statement[] constructAGTemplate(final String contextPath, final Procedure p, final int currentLine,
			final int pp) {
		final Statement[] agAST = new Statement[3];
		// nondeterministic if break
		agAST[0] = agAST[0] = nonDetRet(contextPath, p, currentLine);
		// left hand call
		agAST[1] = this.lcall(contextPath, p, currentLine, "L",
				new IntegerLiteral(LocationProvider.getLocation(), Integer.toString(pp)));
		// return if not true
		agAST[2] = new IfStatement(LocationProvider.getLocation(),
				new UnaryExpression(LocationProvider.getLocation(), Operator.LOGICNEG,
						new IdentifierExpression(LocationProvider.getLocation(), "ret")),
				new Statement[] { new ReturnStatement(LocationProvider.getLocation()) }, new Statement[0]);

		return agAST;
	}

	/**
	 * Generates the code for an AW case
	 *
	 * @param contextPath
	 * @param p
	 * @param currentLine
	 * @return the code for an AW in Cooks algorithm
	 * @see programFragmentTemplate
	 *
	 *      <code>
	 * if (*) {ret:= true; return;}
	 * call ret:= encKL(S, pp);
	 * if (!ret){
	 *  call ret:= encKR(S, pp);
	 * 	ret:= false; return;
	 * }
	 * </code>
	 */
	private Statement[] constructAWTemplate(final String contextPath, final Procedure p, final int currentLine,
			final int pp) {
		final Statement[] agAST = new Statement[3];
		// nondeterministic if break
		agAST[0] = nonDetRet(contextPath, p, currentLine);
		// left hand call
		agAST[1] = this.lcall(contextPath, p, currentLine, "L",
				new IntegerLiteral(LocationProvider.getLocation(), Integer.toString(pp)));
		// return if not true
		agAST[2] = new IfStatement(LocationProvider.getLocation(),
				new UnaryExpression(LocationProvider.getLocation(), Operator.LOGICNEG,
						new IdentifierExpression(LocationProvider.getLocation(), "ret")),
				new Statement[] {
						this.lcall(contextPath, p, currentLine, "R",
								new IntegerLiteral(LocationProvider.getLocation(), Integer.toString(pp))),
						new ReturnStatement(LocationProvider.getLocation()) },
				new Statement[0]);

		return agAST;
	}

	/**
	 * Convert an array of strings into VariableLHS needed for call and havoc. We use the LocationProvider to generate
	 * locations.
	 *
	 * @param ids
	 *            the array of variable identifiers.
	 * @return the corresponding array of VariableLHS objects (type is not set).
	 */
	private static VariableLHS[] makeVariableLHS(final String[] ids) {
		final VariableLHS[] result = new VariableLHS[ids.length];
		for (int i = 0; i < ids.length; i++) {
			result[i] = new VariableLHS(LocationProvider.getLocation(), ids[i]);
		}
		return result;
	}

	/**
	 * returns the code for a logical call according to "Cookiefy"
	 *
	 * @param contextPath
	 * @param p
	 * @param currentLine
	 * @param branch
	 * @return
	 */
	private Statement lcall(final String contextPath, final Procedure p, final int currentLine, final String branch,
			final Expression pp) {
		final VariableLHS[] ret = new VariableLHS[] { new VariableLHS(LocationProvider.getLocation(), "ret") };
		return new CallStatement(LocationProvider.getLocation(), false, ret, methodeNameGen(p, contextPath, branch),
				this.concatToEncArgs(p, pp));
	}

	private Statement lcall(final String contextPath, final Procedure p, final int currentLine, final String branch) {
		// if no pp Expression is given, we set in the variable
		return lcall(contextPath, p, currentLine, branch,
				new IdentifierExpression(LocationProvider.getLocation(), mPPVar.getIdentifiers()[0]));
	}

	/**
	 * returns the nondeterministic if/return code
	 *
	 * @param contextPath
	 * @param p
	 * @param currentLine
	 * @param branch
	 * @return
	 *
	 * 		<code>
	 * if (*) {ret:= true; return;}
	 * </code>
	 */
	private static Statement nonDetRet(final String contextPath, final Procedure p, final int currentLine) {
		return new IfStatement(LocationProvider.getLocation(), new WildcardExpression(LocationProvider.getLocation()),
				new Statement[] {
						new AssignmentStatement(LocationProvider.getLocation(),
								new LeftHandSide[] { new VariableLHS(LocationProvider.getLocation(), "ret") },
								new Expression[] { new BooleanLiteral(LocationProvider.getLocation(), true) }),
						new ReturnStatement(LocationProvider.getLocation()) },
				new Statement[0]);
	}

	/**
	 * Generates the code for an AW case
	 *
	 * @param expr
	 *            the atomic proposition from the ACTL formula.
	 * @return AST segment returning the truth value of the atomic proposition expr
	 * @see programFragmentTemplate
	 *
	 *      <code>
	 * ret:= <expr>;
	 * return;
	 * </code>
	 */
	private static Statement[] atomicPropositionTemplate(final Expression expr) {
		final Statement[] assign = new Statement[] { new AssignmentStatement(LocationProvider.getLocation(),
				new VariableLHS[] { new VariableLHS(LocationProvider.getLocation(), "ret") },
				new Expression[] { expr }), new ReturnStatement(LocationProvider.getLocation()) };
		return assign;
	}

	/**
	 * Generates the code for the Cookiefy - main program entry.
	 *
	 * @param entryPoint
	 *            Name of the entry point procedure of the input program (e.g. 'main')
	 * @return
	 *
	 * 		<code>
	 * procedure main() returns ()
	 * modifies retVal_int;
	 * {
	 *     var CookiefyRet : bool;
	 *     var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
	 *
	 *     var ...
	 *     havoc ...;
	 *
	 *     call CookiefyRet := enc_havoc_main_T(..., intStack, boolStack, idStack, ppStack, sp, 0);
	 *     assert CookiefyRet != false;
	 * }
	 * </code>
	 */
	public Procedure programEntryPointTemplate(final String entryPoint, final Map<String, Expression> entyPointInit,
			final Map<String, Expression> globalVarsInit) {
		//
		// Initialize Variables
		//
		// VariableDeclaration[] params =
		// cookifyArgsDeclareLocals(InputProgram.Procedures.get(entryPoint),true);

		final List<String> modifiesIdentifiers = new LinkedList<>();
		final List<Expression> parameters = new LinkedList<>();
		final List<Statement> statements = new LinkedList<>();
		final List<VariableDeclaration> localVars = new LinkedList<>();
		final Procedure main = mInputProgram.mProcedures.get(entryPoint);

		//
		// havoc all global variables variables
		//
		// globals (from input program)
		for (final VarList v : mGlobalStateVars) {
			// must get modifies specification, because of the havoc
			for (final String id : v.getIdentifiers()) {
				modifiesIdentifiers.add(id);
			}
			Helper.addVarListToIdentifierList(parameters, v);
			// havoc this global variable
			statements.add(new HavocStatement(LocationProvider.getLocation(), makeVariableLHS(v.getIdentifiers())));
		}
		// stacks (add to parameters)
		for (final VarList v : mStack.getVariables()) {
			Helper.addVarListToIdentifierList(parameters, v);
		}
		// pp (=0)
		parameters.add(new IntegerLiteral(LocationProvider.getLocation(), "0"));

		//
		// local vars
		//
		localVars.add(new VariableDeclaration(LocationProvider.getLocation(), new Attribute[0],
				new VarList[] { new VarList(LocationProvider.getLocation(), new String[] { "CookiefyRet" },
						new PrimitiveType(LocationProvider.getLocation(), "bool")) }));
		localVars.add(mStack);
		localVars.add(new VariableDeclaration(LocationProvider.getLocation(), new Attribute[0], mGlobalStateVars));

		final Body body = new Body(LocationProvider.getLocation(),
				localVars.toArray(new VariableDeclaration[localVars.size()]),
				new Statement[] {
						new HavocStatement(LocationProvider.getLocation(),
								makeVariableLHS(modifiesIdentifiers.toArray(new String[modifiesIdentifiers.size()]))),
						// this.getHavocCallStatement(new Expression[0], main,
						// "T", new IntegerLiteral("0")),
						new CallStatement(LocationProvider.getLocation(), false,
								makeVariableLHS(new String[] { "CookiefyRet" }), methodeNameGenPrepare(main, "T", ""),
								parameters.toArray(new Expression[parameters.size()])),
						new AssertStatement(LocationProvider.getLocation(),
								new BinaryExpression(LocationProvider.getLocation(), BinaryExpression.Operator.COMPNEQ,
										new IdentifierExpression(LocationProvider.getLocation(), "CookiefyRet"),
										new BooleanLiteral(LocationProvider.getLocation(), false))) });

		return new Procedure(LocationProvider.getLocation(), new Attribute[0], "main", // identifier
																						// of
				// this
				// procedure
				new String[0], // type params
				new VarList[0], // inParams
				new VarList[0], // outParams
				new Specification[0], // specification
				body);
	}

	/**
	 * Generates the procedure name for the intermediate's procedure havoc form (output program)
	 *
	 * @param p
	 *            procedure the method name shall be generated for
	 * @param path
	 *            current context path
	 * @param branch
	 *            the branch to take from path now
	 * @return enc_ident_contextpath{L|R}
	 *
	 *         Example: enc_havoc_main_T
	 */
	public String methodeNameGenPrepare(final Procedure pPrime, final String path, final String branch) {
		return methodNameGen("havoc_" + pPrime.getIdentifier(), path, branch);
	}

	/**
	 * Generates the procedure name for the procedure's encoded form (output program)
	 *
	 * @param p
	 *            procedure the method name shall be generated for
	 * @param path
	 *            current context path
	 * @param branch
	 *            the branch to take from path now
	 * @return enc_ident_contextpath{L|R}
	 *
	 *         Example: enc_havoc_main_T
	 */
	public String methodeNameGen(final Procedure p, final String path, final String branch) {
		return methodNameGen(p.getIdentifier(), path, branch);
	}

	public String methodNameGen(final String p_identifier, final String path, final String branch) {
		return "enc_" + p_identifier + "_" + path + branch;
	}

	/**
	 * Append local, in, out, global, stack and pp to a parameter list for the procedure call argument list.
	 *
	 * @param p
	 * @return
	 *
	 * 		<code>
	 * varname, *
	 * </code>
	 */
	public Expression[] concatToEncArgs(final Procedure p, final Expression pp) {
		final ArrayList<Expression> idents = new ArrayList<>();

		// in parameters of p
		for (final VarList v : p.getInParams()) {
			for (final String s : v.getIdentifiers()) {
				idents.add(new IdentifierExpression(LocationProvider.getLocation(), s));
			}
		}
		// out parameters of p
		for (final VarList v : p.getOutParams()) {
			for (final String s : v.getIdentifiers()) {
				idents.add(new IdentifierExpression(LocationProvider.getLocation(), s));
			}
		}
		// local variables of p
		for (final VariableDeclaration vd : p.getBody().getLocalVars()) {
			for (final VarList v : vd.getVariables()) {
				for (final String s : v.getIdentifiers()) {
					idents.add(new IdentifierExpression(LocationProvider.getLocation(), s));
				}
			}
		}
		// globals
		for (final VarList v : mGlobalStateVars) {
			for (final String s : v.getIdentifiers()) {
				idents.add(new IdentifierExpression(LocationProvider.getLocation(), s));
			}
		}
		// stack
		for (final VarList v : mStack.getVariables()) {
			for (final String s : v.getIdentifiers()) {
				idents.add(new IdentifierExpression(LocationProvider.getLocation(), s));
			}
		}
		// program counter
		idents.add(pp);

		return idents.toArray(new Expression[idents.size()]);
	}

	public Expression[] concatToEncArgs(final Procedure p) {
		return concatToEncArgs(p, new IdentifierExpression(LocationProvider.getLocation(), mPPVar.getIdentifiers()[0]));
	}

	/**
	 * Assigns the value of the cookiefy_arg_... variables to local vars of the functions for being writable locals with
	 * their original name.
	 *
	 * @param p
	 * @return
	 *
	 * 		<code>
	 * intStack := cookiefy_args_intStack;
	 * boolStack := cookiefy_args_boolStack;
	 * idStack := cookiefy_args_idStack;
	 * ppStack := cookiefy_args_ppStack;
	 *  ...
	 * </code>
	 */
	public Statement[] cookifyArgsToVariables(final Procedure p) {
		final ArrayList<Statement> assignments = new ArrayList<>();

		// LAMBDA
		// Args (in parameters of p)
		for (final VarList v : p.getInParams()) {
			assignments.addAll(prefixVarToLocalVar(v, mParameterToVariablePrefix));
		}

		for (final VarList v : p.getOutParams()) {
			assignments.addAll(prefixVarToLocalVar(v, mParameterToVariablePrefix));
		}
		// Locals (local variables of p)
		for (final VariableDeclaration vd : p.getBody().getLocalVars()) {
			for (final VarList v : vd.getVariables()) {
				assignments.addAll(prefixVarToLocalVar(v, mParameterToVariablePrefix));
			}
		}

		for (final VarList v : mStack.getVariables()) {
			assignments.addAll(prefixVarToLocalVar(v, mParameterToVariablePrefix));
		}

		// GAMMA
		// globals
		for (final VarList v : mGlobalStateVars) {
			assignments.addAll(prefixVarToLocalVar(v, mParameterToVariablePrefix));
		}

		return assignments.toArray(new Statement[assignments.size()]);
	}

	/**
	 * generates the variable declarations for the variables of a procedure
	 *
	 * @param p
	 * @return
	 *
	 * 		<code>
	 * var bla : int;
	 * var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
	 * var foo : bool;
	 * </code>
	 */
	public VariableDeclaration[] cookifyArgsDeclareLocals(final Procedure p, final boolean withStack,
			final boolean withGlobals) {
		final ArrayList<VariableDeclaration> declarations = new ArrayList<>();

		// LAMBDA
		// Args (in parameters of p)
		if (p.getInParams().length > 0) {
			declarations
					.add(new VariableDeclaration(LocationProvider.getLocation(), new Attribute[] {}, p.getInParams()));
		}
		if (p.getOutParams().length > 0) {
			declarations
					.add(new VariableDeclaration(LocationProvider.getLocation(), new Attribute[] {}, p.getOutParams()));
		}
		// Locals (local variables of p)
		for (final VariableDeclaration vd : p.getBody().getLocalVars()) {
			if (vd.getVariables().length > 0) {
				declarations.add(
						new VariableDeclaration(LocationProvider.getLocation(), new Attribute[] {}, vd.getVariables()));
			}
		}

		if (withStack) {
			declarations.add(mStack);
		}

		// GAMMA
		// globals
		if (withGlobals && mGlobalStateVars.length > 0) {
			declarations
					.add(new VariableDeclaration(LocationProvider.getLocation(), new Attribute[] {}, mGlobalStateVars));
		}

		return declarations.toArray(new VariableDeclaration[declarations.size()]);
	}

	/**
	 * append local, in, out, global, stack and pp to a parameter list for the procedure declaration parameter list:
	 * varname:type,*
	 *
	 * @param p
	 * @return
	 *
	 * 		<code>
	 * cookiefy_args_bla:int, cookiefy_args_foo:bool, cookiefy_args_intStack:iStack, cookiefy_args_boolStack:bStack, ...
	 * </code>
	 */
	public VarList[] concatToEncParams(final Procedure p) {
		final ArrayList<VarList> idents = new ArrayList<>();

		// LAMBDA
		// Args (in parameters of p)
		for (final VarList v : p.getInParams()) {
			Helper.addVarListToArrayList(idents, v, mParameterToVariablePrefix);
		}
		// return
		for (final VarList v : p.getOutParams()) {
			Helper.addVarListToArrayList(idents, v, mParameterToVariablePrefix);
		}
		// Locals (local variables of p)
		for (final VariableDeclaration vd : p.getBody().getLocalVars()) {
			for (final VarList v : vd.getVariables()) {
				Helper.addVarListToArrayList(idents, v, mParameterToVariablePrefix);
			}
		}

		// GAMMA
		// globals
		for (final VarList v : mGlobalStateVars) {
			Helper.addVarListToArrayList(idents, v, mParameterToVariablePrefix);
		}

		// stack
		for (final VarList v : mStack.getVariables()) {
			Helper.addVarListToArrayList(idents, v, mParameterToVariablePrefix);
		}

		// program counter
		idents.add(mPPVar);

		return idents.toArray(new VarList[idents.size()]);
	}

	/**
	 * Parametes for procedure calls
	 *
	 * @param p
	 * @return
	 *
	 * 		<code>
	 *  intStack, boolStack, idStack, ppStack, sp, ...
	 * </code>
	 */
	public VarList[] concatToEncParamsAtom(final Procedure p) {
		final ArrayList<VarList> idents = new ArrayList<>();

		// LAMBDA
		// Args (in parameters of p)
		for (final VarList v : p.getInParams()) {
			Helper.addVarListToArrayList(idents, v, "");
		}
		// return
		for (final VarList v : p.getOutParams()) {
			Helper.addVarListToArrayList(idents, v, "");
		}
		// Locals (local variables of p)
		for (final VariableDeclaration vd : p.getBody().getLocalVars()) {
			for (final VarList v : vd.getVariables()) {
				Helper.addVarListToArrayList(idents, v, "");
			}
		}

		// GAMMA
		// globals
		for (final VarList v : mGlobalStateVars) {
			Helper.addVarListToArrayList(idents, v, "");
		}

		// stack
		for (final VarList v : mStack.getVariables()) {
			Helper.addVarListToArrayList(idents, v, "");
		}

		// program counter
		idents.add(mPPVar);

		return idents.toArray(new VarList[idents.size()]);
	}

	/**
	 * set the list of global variables for the function arguments
	 *
	 * @param vd
	 */
	private void setGlobalStateVars() {
		final ArrayList<VarList> vars = new ArrayList<>();

		for (final VariableDeclaration vdecl : mInputProgram.mGlobals) {
			for (final VarList vlist : vdecl.getVariables()) {
				Helper.addVarListToArrayList(vars, vlist, "");
			}
		}

		mGlobalStateVars = vars.toArray(new VarList[vars.size()]);
	}

	/**
	 * Generates one line for cookifyArgsToVariables
	 *
	 * @param v
	 * @param prefix
	 * @return
	 *
	 * 		<code>
	 * bla := cookiefy_args_bla;
	 * </code>
	 */
	private static ArrayList<Statement> prefixVarToLocalVar(final VarList v, final String prefix) {
		final ArrayList<Statement> assignments = new ArrayList<>();
		for (final String s : v.getIdentifiers()) {
			assignments.add(new AssignmentStatement(LocationProvider.getLocation(),
					new LeftHandSide[] { new VariableLHS(LocationProvider.getLocation(), s) }, new Expression[] {
							new IdentifierExpression(LocationProvider.getLocation(), "cookiefy_args_" + s) }));
		}
		return assignments;
	}

	/**
	 * Generates the pcall intermediate procedure.
	 *
	 * @param pPrime
	 *            callee
	 * @param kappa
	 *            context path
	 * @return
	 *
	 * 		<code>
	 * procedure enc_havoc_main_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
	 * {
	 *  var bla : int;
	 *
	 *  havoc bla;
	 *  call ret := enc_main_T(bla, foo, intStack, boolStack, idStack, ppStack, sp, pp);
	 * }
	 * </code>
	 */
	public Procedure encodeInitProcedurestateProcedure(final Procedure pPrime, final String path,
			final Expression[] args) {
		final ArrayList<Statement> body = new ArrayList<>();
		// prepare params for the havoc_... procedure
		final ArrayList<VarList> params = new ArrayList<>();
		for (final VarList v : pPrime.getInParams()) {
			Helper.addVarListToArrayList(params, v, mParameterToVariablePrefix);
		}
		// globals
		for (final VarList v : mGlobalStateVars) {
			Helper.addVarListToArrayList(params, v, "");
		}
		for (final VarList v : mStack.getVariables()) {
			Helper.addVarListToArrayList(params, v, "");
		}
		params.add(mPPVar);
		// pp = 0!

		// declaration is done in the procedure declaration
		// havoc Vars
		for (final VarList v : pPrime.getInParams()) {
			body.add(new HavocStatement(LocationProvider.getLocation(), makeVariableLHS(v.getIdentifiers())));
		}
		for (final VarList v : pPrime.getOutParams()) {
			body.add(new HavocStatement(LocationProvider.getLocation(), makeVariableLHS(v.getIdentifiers())));
		}
		for (final VariableDeclaration vd : pPrime.getBody().getLocalVars()) {
			for (final VarList v : vd.getVariables()) {
				body.add(new HavocStatement(LocationProvider.getLocation(), makeVariableLHS(v.getIdentifiers())));
			}
		}

		// copy arguments to vars
		for (final VarList v : pPrime.getInParams()) {
			for (final String ident : v.getIdentifiers()) {
				body.add(new AssignmentStatement(LocationProvider.getLocation(),
						new LeftHandSide[] { new VariableLHS(LocationProvider.getLocation(), ident) },
						new Expression[] { new IdentifierExpression(LocationProvider.getLocation(),
								mParameterToVariablePrefix + ident) }));
			}
		}

		// call procedure
		body.add(new CallStatement(LocationProvider.getLocation(), false, makeVariableLHS(new String[] { "ret" }),
				methodeNameGen(pPrime, path, ""), this.concatToEncArgs(pPrime)));

		return new Procedure(LocationProvider.getLocation(), new Attribute[0], methodeNameGenPrepare(pPrime, path, ""),
				new String[0], params.toArray(new VarList[params.size()]),
				new VarList[] { new VarList(LocationProvider.getLocation(), new String[] { "ret" },
						new PrimitiveType(LocationProvider.getLocation(), "bool")) },
				new Specification[0], new Body(LocationProvider.getLocation(),
						cookifyArgsDeclareLocals(pPrime, false, false), body.toArray(new Statement[body.size()]))

		);

	}

	/**
	 * Pushs a varlist to the pcall-stack
	 *
	 * @param varLists
	 * @return code for stack.push
	 *
	 *         <code>
	 * intStack[sp][0] := i;
	 * intStack[sp][1] := v;
	 * ppStack[sp] := 4;
	 * idStack[sp] := 1;
	 * </code>
	 */
	private ArrayList<Statement> pushVarListToStack(final VarList[] varLists) {
		final ArrayList<Statement> statements = new ArrayList<>();
		Expression noExp = null;
		// in parameters of p
		for (final VarList v : varLists) {
			for (final String s : v.getIdentifiers()) {

				if (((PrimitiveType) v.getType()).getName() == "int") {
					noExp = new IntegerLiteral(LocationProvider.getLocation(), Integer.toString(mIntStackFrameCounter));
				}
				if (((PrimitiveType) v.getType()).getName() == "bool") {
					noExp = new IntegerLiteral(LocationProvider.getLocation(),
							Integer.toString(mBoolStackFrameCounter));
				}

				statements.add(new AssignmentStatement(LocationProvider.getLocation(), new LeftHandSide[] {
						new ArrayLHS(LocationProvider.getLocation(), new ArrayLHS(LocationProvider.getLocation(),
								new VariableLHS(LocationProvider.getLocation(), getStackFromType(v.getType())),
								new Expression[] { new IdentifierExpression(LocationProvider.getLocation(), "sp") }),
								new Expression[] { noExp }) },
						new Expression[] { new IdentifierExpression(LocationProvider.getLocation(), s) }

				));
				if (v.getType() instanceof PrimitiveType) {
					if (((PrimitiveType) v.getType()).getName() == "int") {
						mIntStackFrameCounter++;
					}
					if (((PrimitiveType) v.getType()).getName() == "bool") {
						mBoolStackFrameCounter++;
					}
				}

			}
		}
		return statements;
	}

	/**
	 * Pops from the pcall-stack
	 *
	 * @param varLists
	 * @return code for stack.push
	 *
	 *         <code>
	 * intStack[sp][0], intStack[sp][1]
	 * </code>
	 */
	private ArrayList<Expression> popVarsFromStack(final VarList[] varLists) {
		final ArrayList<Expression> expressions = new ArrayList<>();
		Expression noExp = null;
		// in parameters of p
		for (final VarList v : varLists) {
			for (final String s : v.getIdentifiers()) {

				if (((PrimitiveType) v.getType()).getName() == "int") {
					noExp = new IntegerLiteral(LocationProvider.getLocation(), Integer.toString(mIntStackFrameCounter));
				}
				if (((PrimitiveType) v.getType()).getName() == "bool") {
					noExp = new IntegerLiteral(LocationProvider.getLocation(),
							Integer.toString(mBoolStackFrameCounter));
				}

				expressions.add(new ArrayAccessExpression(LocationProvider.getLocation(),
						new ArrayAccessExpression(LocationProvider.getLocation(),
								new IdentifierExpression(LocationProvider.getLocation(), getStackFromType(v.getType())),
								new Expression[] { new IdentifierExpression(LocationProvider.getLocation(), "sp") }),
						new Expression[] { noExp }));
				if (v.getType() instanceof PrimitiveType) {
					if (((PrimitiveType) v.getType()).getName() == "int") {
						mIntStackFrameCounter++;
					}
					if (((PrimitiveType) v.getType()).getName() == "bool") {
						mBoolStackFrameCounter++;
					}
				}

			}
		}
		return expressions;
	}

	private static String getStackFromType(final ASTType type) {
		if (type instanceof PrimitiveType) {
			if (((PrimitiveType) type).getName() == "int") {
				return "intStack";
			}
			if (((PrimitiveType) type).getName() == "bool") {
				return "boolStack";
			}
		}
		return "error";
	}

	/**
	 * generates the stack push for one procedures statevars.
	 *
	 * @param p
	 * @param mPPVar
	 */
	public Expression[] stackPop(final Procedure p) {
		final ArrayList<Expression> expressions = new ArrayList<>();
		// stack add
		mIntStackFrameCounter = 0;
		mBoolStackFrameCounter = 0;
		// in parameters of p
		expressions.addAll(popVarsFromStack(p.getInParams()));
		// out parameters of p
		expressions.addAll(popVarsFromStack(p.getOutParams()));
		// local variables of p

		for (final VariableDeclaration vd : p.getBody().getLocalVars()) {
			expressions.addAll(popVarsFromStack(vd.getVariables()));
		}

		// globals
		for (final VarList v : mGlobalStateVars) {
			for (final String s : v.getIdentifiers()) {
				expressions.add(new IdentifierExpression(LocationProvider.getLocation(), s));
			}
		}

		// stacks
		for (final VarList v : mStack.getVariables()) {
			for (final String ident : v.getIdentifiers()) {
				if (ident == "sp") {
					expressions.add(
							new BinaryExpression(LocationProvider.getLocation(), BinaryExpression.Operator.ARITHMINUS,
									new IdentifierExpression(LocationProvider.getLocation(), "sp"),
									new IntegerLiteral(LocationProvider.getLocation(), "1")));
				} else {
					expressions.add(new IdentifierExpression(LocationProvider.getLocation(), ident));
				}

			}
		}
		// pp
		expressions.add(new ArrayAccessExpression(LocationProvider.getLocation(),
				new IdentifierExpression(LocationProvider.getLocation(), "ppStack"),
				new Expression[] { new IdentifierExpression(LocationProvider.getLocation(), "sp") }));

		return expressions.toArray(new Expression[expressions.size()]);
	}

	/**
	 * generates the stack push for one procedures statevars.
	 *
	 * @param p
	 * @param pp
	 */
	public List<Statement> stackPush(final Procedure p, final int pp) {
		mIntStackFrameCounter = 0;
		mBoolStackFrameCounter = 0;
		final ArrayList<Statement> statements = new ArrayList<>();
		// in parameters of p
		statements.addAll(pushVarListToStack(p.getInParams()));
		// out parameters of p
		statements.addAll(pushVarListToStack(p.getOutParams()));
		// local variables of p

		for (final VariableDeclaration vd : p.getBody().getLocalVars()) {
			statements.addAll(pushVarListToStack(vd.getVariables()));
		}

		// pp
		statements.add(new AssignmentStatement(LocationProvider.getLocation(),
				new LeftHandSide[] { new ArrayLHS(LocationProvider.getLocation(),
						new VariableLHS(LocationProvider.getLocation(), "ppStack"),
						new Expression[] { new IdentifierExpression(LocationProvider.getLocation(), "sp") }) },
				new Expression[] { new IntegerLiteral(LocationProvider.getLocation(), Integer.toString(pp)) }

		));
		// id
		statements.add(new AssignmentStatement(LocationProvider.getLocation(),
				new LeftHandSide[] { new ArrayLHS(LocationProvider.getLocation(),
						new VariableLHS(LocationProvider.getLocation(), "idStack"),
						new Expression[] { new IdentifierExpression(LocationProvider.getLocation(), "sp") }) },
				new Expression[] { new IntegerLiteral(LocationProvider.getLocation(),
						Integer.toString(mIdentMap.getID(p.getIdentifier()))) }

		));

		return statements;
	}

	/**
	 * generates the call statement for one havoc_ procedure
	 *
	 * @param pPrime
	 * @param path
	 * @param value
	 *            for sp (only used by main entry point to set this to zero)
	 * @return
	 *
	 * 		<code>
	 * call ret := enc_havoc_recursive_T(0, ..., intStack, boolStack, idStack, ppStack, sp + 1, 0);
	 * </code>
	 */
	public Statement getHavocCallStatement(final Expression[] args, final Procedure pPrime, final String path,
			final Expression sp) {

		final ArrayList<Expression> params = new ArrayList<>();
		for (final Expression e : args) {
			params.add(e);
		}

		// globals
		for (final VarList v : mGlobalStateVars) {
			Helper.addVarListToIdentifierList(params, v);
		}

		// stacks
		for (final VarList v : mStack.getVariables()) {
			for (final String ident : v.getIdentifiers()) {
				if (ident == "sp") {
					params.add(sp);
				} else {
					params.add(new IdentifierExpression(LocationProvider.getLocation(), ident));
				}

			}
		}
		// pp
		params.add(new IntegerLiteral(LocationProvider.getLocation(), "0"));

		return new CallStatement(LocationProvider.getLocation(), false, makeVariableLHS(new String[] { "ret" }),
				methodeNameGenPrepare(pPrime, path, ""), params.toArray(new Expression[params.size()]));

	}

	public Statement getHavocCallStatement(final Expression[] args, final Procedure pPrime, final String path) {
		return getHavocCallStatement(args, pPrime, path,
				new BinaryExpression(LocationProvider.getLocation(), BinaryExpression.Operator.ARITHPLUS,
						new IdentifierExpression(LocationProvider.getLocation(), "sp"),
						new IntegerLiteral(LocationProvider.getLocation(), "1")));
	}

	/**
	 * creates a Call statement that calls the corresponding preturn_K function
	 *
	 * @param path
	 * @return
	 *
	 * 		<code>
	 * call ret := preturn_T(..., intStack, boolStack, idStack, ppStack, sp);
	 * </code>
	 */
	public CallStatement pReturnCall(final String path) {
		final ArrayList<Expression> params = new ArrayList<>();

		// globals
		for (final VarList v : mGlobalStateVars) {
			Helper.addVarListToIdentifierList(params, v);
		}
		// stacks
		for (final VarList v : mStack.getVariables()) {
			for (final String ident : v.getIdentifiers()) {
				params.add(new IdentifierExpression(LocationProvider.getLocation(), ident));

			}
		}

		return new CallStatement(LocationProvider.getLocation(), false, makeVariableLHS(new String[] { "ret" }),
				"preturn_" + path, params.toArray(new Expression[params.size()]));

	}

	/**
	 * generiter die preturn funktionen mit goto listen darin
	 *
	 * @param path
	 * @return
	 *
	 * 		<code>
	 * procedure preturn_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
	 * 	modifies retVal_int;
	 * 	{
	 * 	    var func_id : int;
	 *
	 * 	    func_id := idStack[sp];
	 * 	    if (func_id == 0) {
	 * 	        call ret := enc_main_T(intStack[sp][0], foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
	 * 	    }
	 * 	    if (func_id == 1) {
	 * 	        call ret := enc_recursive_T(intStack[sp][0], intStack[sp][1], foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
	 * 	    }
	 * 	}
	 * 	</code>
	 */
	public Procedure pReturn(final String path) {
		final ArrayList<Statement> statements = new ArrayList<>();
		statements.add(new AssignmentStatement(LocationProvider.getLocation(),
				new LeftHandSide[] { new VariableLHS(LocationProvider.getLocation(), "func_id") },
				new Expression[] { new ArrayAccessExpression(LocationProvider.getLocation(),
						new IdentifierExpression(LocationProvider.getLocation(), "idStack"),
						new Expression[] { new IdentifierExpression(LocationProvider.getLocation(), "sp") }) }));

		// for every procedure in the program add a sp -> procedure call
		for (final String pName : mInputProgram.mProcedures.keySet()) {
			final Procedure p = mInputProgram.mProcedures.get(pName);

			statements.add(new IfStatement(LocationProvider.getLocation(),
					new BinaryExpression(LocationProvider.getLocation(), BinaryExpression.Operator.COMPEQ,
							new IdentifierExpression(LocationProvider.getLocation(), "func_id"),
							new IntegerLiteral(LocationProvider.getLocation(),
									Integer.toString(mIdentMap.getID(pName)))),
					new Statement[] {
							// the actual call doing the returning... wtf
							new CallStatement(LocationProvider.getLocation(), false,
									makeVariableLHS(new String[] { "ret" }), methodeNameGen(p, path, ""),
									stackPop(p)) },
					new Statement[] {}

			));
		}

		final ArrayList<VarList> idents = new ArrayList<>();
		// globals
		for (final VarList v : mGlobalStateVars) {
			Helper.addVarListToArrayList(idents, v, "");
		}
		// stack
		for (final VarList v : mStack.getVariables()) {
			Helper.addVarListToArrayList(idents, v, "");
			// program counter
			// idents.add(this.pp); //Jeremi: preturn braucht keinen procedure
			// counter!
		}

		return new Procedure(LocationProvider.getLocation(), new Attribute[] {}, "preturn_" + path, new String[] {},
				idents.toArray(new VarList[idents.size()]),
				new VarList[] { new VarList(LocationProvider.getLocation(), new String[] { "ret" },
						new PrimitiveType(LocationProvider.getLocation(), "bool")) },
				new Specification[] {},
				new Body(LocationProvider.getLocation(),
						new VariableDeclaration[] { new VariableDeclaration(LocationProvider.getLocation(),
								new Attribute[] {},
								new VarList[] { new VarList(LocationProvider.getLocation(), new String[] { "func_id" },
										new PrimitiveType(LocationProvider.getLocation(), "int")) }) },
						statements.toArray(new Statement[statements.size()])));
	}

}
