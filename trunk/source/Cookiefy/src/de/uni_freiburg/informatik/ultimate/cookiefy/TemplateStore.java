package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.cookiefy.ContextPath.ContextPathAlphaNode;
import de.uni_freiburg.informatik.ultimate.cookiefy.ContextPath.ContextPathNode;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;

/**
 * Stores the templates for the Boogiepl code inserted by cookiefy.
 * 
 * procedure format enc_id_K(locals..., globals..., stack: stack, pp:int)
 * 
 * @author Vincent, Jeremi
 */
public class TemplateStore {

	protected static Logger logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	private String filename = "Cook Annotation";

	/**
	 * VarList is the array of global state vars.
	 */
	private VarList[] globalStateVars;

	public VarList[] getGlobalStateVars() {
		return globalStateVars;
	}

	// this has to be refactored !!!!
	private int intStackFrameCounter = 0;
	private int boolStackFrameCounter = 0;

	// ?
	private IdentMap identMap = new IdentMap();

	/**
	 * AST Prototype for the type definition of the int stack.
	 * 
	 * <code>
	 * type iStack = [int][int]int;
	 * </code>
	 */
	public TypeDeclaration iStackType = new TypeDeclaration(
			LocationProvider.getLocation(), new Attribute[] {}, false,
			"iStack", new String[] {}, new ArrayType(
					LocationProvider.getLocation(), new String[] {},
					new ASTType[] { new PrimitiveType(LocationProvider
							.getLocation(), "int") },
					new ArrayType(LocationProvider.getLocation(),
							new String[] {}, new ASTType[] { new PrimitiveType(
									LocationProvider.getLocation(), "int") },
							new PrimitiveType(LocationProvider.getLocation(),
									"int"))));

	/**
	 * AST Prototype for the type definition of the bool stack.
	 * 
	 * <code>
	 * type bStack = [int][int]bool;
	 * </code>
	 */
	public TypeDeclaration bStackType = new TypeDeclaration(
			LocationProvider.getLocation(), new Attribute[] {}, false,
			"bStack", new String[] {}, new ArrayType(
					LocationProvider.getLocation(), new String[] {},
					new ASTType[] { new PrimitiveType(LocationProvider
							.getLocation(), "int") },
					new ArrayType(LocationProvider.getLocation(),
							new String[] {}, new ASTType[] { new PrimitiveType(
									LocationProvider.getLocation(), "int") },
							new PrimitiveType(LocationProvider.getLocation(),
									"bool"))));

	/**
	 * AST Prototype for the type definition of the integer array.
	 * 
	 * <code>
	 * type iArray = [int]int;
	 * </code>
	 */
	public TypeDeclaration iArrayType = new TypeDeclaration(
			LocationProvider.getLocation(), new Attribute[] {}, false,
			"iArray", new String[] {}, new ArrayType(
					LocationProvider.getLocation(), new String[] {},
					new ASTType[] { new PrimitiveType(LocationProvider
							.getLocation(), "int") },
					new PrimitiveType(LocationProvider.getLocation(), "int")));

	/**
	 * AST Prototype for the type definition of the stacks.
	 * 
	 * <code>
	 * var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
	 * </code>
	 */
	private VariableDeclaration stack = new VariableDeclaration(
			LocationProvider.getLocation(), new Attribute[] {}, new VarList[] {
					new VarList(LocationProvider.getLocation(),
							new String[] { "intStack" }, new NamedType(
									LocationProvider.getLocation(), "iStack",
									new ASTType[] {})),
					new VarList(LocationProvider.getLocation(),
							new String[] { "boolStack" }, new NamedType(
									LocationProvider.getLocation(), "bStack",
									new ASTType[] {})),
					new VarList(LocationProvider.getLocation(),
							new String[] { "idStack" }, new NamedType(
									LocationProvider.getLocation(), "iArray",
									new ASTType[] {})),
					new VarList(LocationProvider.getLocation(),
							new String[] { "ppStack" }, new NamedType(
									LocationProvider.getLocation(), "iArray",
									new ASTType[] {})),
					new VarList(LocationProvider.getLocation(),
							new String[] { "sp" }, new PrimitiveType(
									LocationProvider.getLocation(), "int")) });

	/**
	 * AST Prototype for the type definition of the stacks.
	 * 
	 * <code>
	 * pp:int
	 * </code>
	 */
	private VarList pp = new VarList(LocationProvider.getLocation(),
			new String[] { "pp" }, new PrimitiveType(
					LocationProvider.getLocation(), "int"));

	/**
	 * Prefix for cookiefy generated procedure arguments
	 */
	private String parameterToVariablePrefix = "cookiefy_args_";

	private Program InputProgram;

	public Program getInputProgram() {
		return InputProgram;
	}

	/**
	 * initializes a new template store for the given unit
	 * 
	 * @param u
	 *            unit generated for
	 */
	public TemplateStore(Program program) {
		InputProgram = program;
		this.setGlobalStateVars();
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
	public Statement[] programFragmentTemplate(ContextPathNode cp, Procedure p,
			int pp) {
		switch (cp.getFormulaType()) {
		case Alpha:
			Expression expr = ((ContextPathAlphaNode) cp).getExpression();
			return atomicPropositionTemplate(expr);
		case And:
			return andTemplate(cp.getPath(), p, pp);
		case Or:
			return orTemplate(cp.getPath(), p, pp);
		case AG:
			return AGTemplate(cp.getPath(), p, pp, pp);
		case AW:
			return AWTemplate(cp.getPath(), p, pp, pp);
		default:
			logger.error("No template found for this property operator!");
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
	private Statement[] andTemplate(String contextPath, Procedure p,
			int currentLine) {
		VariableLHS[] ret = new VariableLHS[] {
				new VariableLHS(LocationProvider.getLocation(), "ret")
		};
		// left branch call
		Statement[] lcallL = new Statement[] { new CallStatement(
				LocationProvider.getLocation(), false, ret,
				this.methodeNameGen(p, contextPath, "L"),
				this.concatToEncArgs(p)) };
		// right branch call
		Statement[] lcallR = new Statement[] { new CallStatement(
				LocationProvider.getLocation(), false, ret,
				this.methodeNameGen(p, contextPath, "R"),
				this.concatToEncArgs(p)) };

		Statement[] andAST = new Statement[] { new IfStatement(
				LocationProvider.getLocation(), new WildcardExpression(
						LocationProvider.getLocation()), lcallL, lcallR) };

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
	private Statement[] orTemplate(String contextPath, Procedure p,
			int currentLine) {
		Statement[] orAST = new Statement[2];
		// left call first
		orAST[0] = this.lcall(contextPath, p, currentLine, "L");
		// right call
		Statement[] lcallR = new Statement[] {
				this.lcall(contextPath, p, currentLine, "R"),
				new ReturnStatement(LocationProvider.getLocation()) };
		// if left then right
		orAST[1] = new IfStatement(
				LocationProvider.getLocation(),
				new IdentifierExpression(LocationProvider.getLocation(), "ret"),
				new Statement[] { new ReturnStatement(LocationProvider
						.getLocation()) }, lcallR);

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
	private Statement[] AGTemplate(String contextPath, Procedure p,
			int currentLine, int pp) {
		Statement[] agAST = new Statement[3];
		// nondeterministic if break
		agAST[0] = agAST[0] = this.nonDetRet(contextPath, p, currentLine);
		// left hand call
		agAST[1] = this.lcall(
				contextPath,
				p,
				currentLine,
				"L",
				new IntegerLiteral(LocationProvider.getLocation(), Integer
						.toString(pp)));
		// return if not true
		agAST[2] = new IfStatement(LocationProvider.getLocation(),
				new UnaryExpression(LocationProvider.getLocation(),
						Operator.LOGICNEG, new IdentifierExpression(
								LocationProvider.getLocation(), "ret")),
				new Statement[] { new ReturnStatement(LocationProvider
						.getLocation()) }, new Statement[0]);

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
	private Statement[] AWTemplate(String contextPath, Procedure p,
			int currentLine, int pp) {
		Statement[] agAST = new Statement[3];
		// nondeterministic if break
		agAST[0] = this.nonDetRet(contextPath, p, currentLine);
		// left hand call
		agAST[1] = this.lcall(
				contextPath,
				p,
				currentLine,
				"L",
				new IntegerLiteral(LocationProvider.getLocation(), Integer
						.toString(pp)));
		// return if not true
		agAST[2] = new IfStatement(LocationProvider.getLocation(),
				new UnaryExpression(LocationProvider.getLocation(),
						Operator.LOGICNEG, new IdentifierExpression(
								LocationProvider.getLocation(), "ret")),
				new Statement[] {
						this.lcall(
								contextPath,
								p,
								currentLine,
								"R",
								new IntegerLiteral(LocationProvider
										.getLocation(), Integer.toString(pp))),
						new ReturnStatement(LocationProvider.getLocation()) },
				new Statement[0]);

		return agAST;
	}
	
	/**
	 * Convert an array of strings into VariableLHS needed for call and havoc.
	 * We use the LocationProvider to generate locations.
	 * @param ids the array of variable identifiers.
	 * @return the corresponding array of VariableLHS objects (type is not set).
	 */
	private VariableLHS[] makeVariableLHS(String[] ids) {
		VariableLHS[] result = new VariableLHS[ids.length];
		for (int i = 0; i < ids.length; i++)
			result[i] = new VariableLHS(LocationProvider.getLocation(), ids[i]);
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
	private Statement lcall(String contextPath, Procedure p, int currentLine,
			String branch, Expression pp) {
		VariableLHS[] ret = new VariableLHS[] {
				new VariableLHS(LocationProvider.getLocation(), "ret")
		};
		return new CallStatement(LocationProvider.getLocation(), false,
				ret, this.methodeNameGen(p, contextPath,
						branch), this.concatToEncArgs(p, pp));
	}

	private Statement lcall(String contextPath, Procedure p, int currentLine,
			String branch) {
		// if no pp Expression is given, we set in the variable
		return lcall(contextPath, p, currentLine, branch,
				new IdentifierExpression(LocationProvider.getLocation(),
						this.pp.getIdentifiers()[0]));
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
	 *         <code>
	 * if (*) {ret:= true; return;}
	 * </code>
	 */
	private Statement nonDetRet(String contextPath, Procedure p, int currentLine) {
		return new IfStatement(
				LocationProvider.getLocation(),
				new WildcardExpression(LocationProvider.getLocation()),
				new Statement[] {
						new AssignmentStatement(
								LocationProvider.getLocation(),
								new LeftHandSide[] { new VariableLHS(
										LocationProvider.getLocation(), "ret") },
								new Expression[] { new BooleanLiteral(
										LocationProvider.getLocation(), true) }),
						new ReturnStatement(LocationProvider.getLocation()) },
				new Statement[0]);
	}

	/**
	 * Generates the code for an AW case
	 * 
	 * @param expr
	 *            the atomic proposition from the ACTL formula.
	 * @return AST segment returning the truth value of the atomic proposition
	 *         expr
	 * @see programFragmentTemplate
	 * 
	 *      <code>
	 * ret:= <expr>;
	 * return;
	 * </code>
	 */
	private Statement[] atomicPropositionTemplate(Expression expr) {
		Statement[] assign = new Statement[] {
				new AssignmentStatement(LocationProvider.getLocation(),
						new VariableLHS[] { new VariableLHS(LocationProvider
								.getLocation(), "ret") },
						new Expression[] { expr }),
				new ReturnStatement(LocationProvider.getLocation()) };
		return assign;
	}

	/**
	 * Generates the code for the Cookiefy - main program entry.
	 * 
	 * @param entryPoint
	 *            Name of the entry point procedure of the input program (e.g.
	 *            'main')
	 * @return
	 * 
	 *         <code>
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
	public Procedure programEntryPointTemplate(String entryPoint,
			Map<String, Expression> entyPointInit,
			Map<String, Expression> globalVarsInit) {
		//
		// Initialize Variables
		//
		// VariableDeclaration[] params =
		// cookifyArgsDeclareLocals(InputProgram.Procedures.get(entryPoint),true);

		List<String> modifiesIdentifiers = new LinkedList<String>();
		List<Expression> parameters = new LinkedList<Expression>();
		List<Statement> statements = new LinkedList<Statement>();
		List<VariableDeclaration> localVars = new LinkedList<VariableDeclaration>();
		Procedure main = InputProgram.Procedures.get(entryPoint);

		//
		// havoc all global variables variables
		//
		// globals (from input program)
		for (VarList v : this.globalStateVars) {
			// must get modifies specification, because of the havoc
			for (String id : v.getIdentifiers()) {
				modifiesIdentifiers.add(id);
			}
			Helper.addVarListToIdentifierList(parameters, v);
			// havoc this global variable
			statements.add(new HavocStatement(LocationProvider.getLocation(), 
					makeVariableLHS(v.getIdentifiers())));
		}
		// stacks (add to parameters)
		for (VarList v : this.stack.getVariables()) {
			Helper.addVarListToIdentifierList(parameters, v);
		}
		// pp (=0)
		parameters.add(new IntegerLiteral(LocationProvider.getLocation(), "0"));

		//
		// local vars
		//
		localVars.add(new VariableDeclaration(LocationProvider.getLocation(),
				new Attribute[0], new VarList[] { new VarList(LocationProvider
						.getLocation(), new String[] { "CookiefyRet" },
						new PrimitiveType(LocationProvider.getLocation(),
								"bool")) }));
		localVars.add(this.stack);
		localVars.add(new VariableDeclaration(LocationProvider.getLocation(),
				new Attribute[0], this.globalStateVars));

		Body body = new Body(LocationProvider.getLocation(),
				localVars.toArray(new VariableDeclaration[localVars.size()]),
				new Statement[] {
						new HavocStatement(LocationProvider.getLocation(),
								makeVariableLHS(
								modifiesIdentifiers
										.toArray(new String[modifiesIdentifiers
												.size()]))),
						// this.getHavocCallStatement(new Expression[0], main,
						// "T", new IntegerLiteral("0")),
						new CallStatement(LocationProvider.getLocation(),
								false, 
								makeVariableLHS(new String[] { "CookiefyRet" }),
								this.methodeNameGenPrepare(main, "T", ""),
								parameters.toArray(new Expression[parameters
										.size()])),
						new AssertStatement(LocationProvider.getLocation(),
								new BinaryExpression(
										LocationProvider.getLocation(),
										BinaryExpression.Operator.COMPNEQ,
										new IdentifierExpression(
												LocationProvider.getLocation(),
												"CookiefyRet"),
										new BooleanLiteral(LocationProvider
												.getLocation(), false))) });

		return new Procedure(LocationProvider.getLocation(), new Attribute[0],
				"main", // identifier of
				// this
				// procedure
				new String[0], // type params
				new VarList[0], // inParams
				new VarList[0], // outParams
				new Specification[0], // specification
				body);
	}

	/**
	 * Generates the procedure name for the intermediate's procedure havoc form
	 * (output program)
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
	public String methodeNameGenPrepare(Procedure pPrime, String path,
			String branch) {
		return methodNameGen("havoc_" + pPrime.getIdentifier(), path, branch);
	}

	/**
	 * Generates the procedure name for the procedure's encoded form (output
	 * program)
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
	public String methodeNameGen(Procedure p, String path, String branch) {
		return methodNameGen(p.getIdentifier(), path, branch);
	}

	public String methodNameGen(String p_identifier, String path, String branch) {
		return "enc_" + p_identifier + "_" + path + branch;
	}

	/**
	 * Append local, in, out, global, stack and pp to a parameter list for the
	 * procedure call argument list.
	 * 
	 * @param p
	 * @return
	 * 
	 *         <code>
	 * varname, *
	 * </code>
	 */
	public Expression[] concatToEncArgs(Procedure p, Expression pp) {
		ArrayList<Expression> idents = new ArrayList<Expression>();

		// in parameters of p
		for (VarList v : p.getInParams())
			for (String s : v.getIdentifiers())
				idents.add(new IdentifierExpression(LocationProvider
						.getLocation(), s));
		// out parameters of p
		for (VarList v : p.getOutParams())
			for (String s : v.getIdentifiers())
				idents.add(new IdentifierExpression(LocationProvider
						.getLocation(), s));
		// local variables of p
		for (VariableDeclaration vd : p.getBody().getLocalVars())
			for (VarList v : vd.getVariables())
				for (String s : v.getIdentifiers())
					idents.add(new IdentifierExpression(LocationProvider
							.getLocation(), s));
		// globals
		for (VarList v : this.globalStateVars)
			for (String s : v.getIdentifiers())
				idents.add(new IdentifierExpression(LocationProvider
						.getLocation(), s));
		// stack
		for (VarList v : this.stack.getVariables())
			for (String s : v.getIdentifiers())
				idents.add(new IdentifierExpression(LocationProvider
						.getLocation(), s));
		// program counter
		idents.add(pp);

		return idents.toArray(new Expression[idents.size()]);
	}

	public Expression[] concatToEncArgs(Procedure p) {
		return concatToEncArgs(p,
				new IdentifierExpression(LocationProvider.getLocation(),
						this.pp.getIdentifiers()[0]));
	}

	/**
	 * Assigns the value of the cookiefy_arg_... variables to local vars of the
	 * functions for being writable locals with their original name.
	 * 
	 * @param p
	 * @return
	 * 
	 *         <code>
	 * intStack := cookiefy_args_intStack;
	 * boolStack := cookiefy_args_boolStack;
	 * idStack := cookiefy_args_idStack;
	 * ppStack := cookiefy_args_ppStack;
	 *  ...
	 * </code>
	 */
	public Statement[] cookifyArgsToVariables(Procedure p) {
		ArrayList<Statement> assignments = new ArrayList<Statement>();

		// LAMBDA
		// Args (in parameters of p)
		for (VarList v : p.getInParams())
			assignments.addAll(this.prefixVarToLocalVar(v,
					parameterToVariablePrefix));

		for (VarList v : p.getOutParams())
			assignments.addAll(this.prefixVarToLocalVar(v,
					parameterToVariablePrefix));
		// Locals (local variables of p)
		for (VariableDeclaration vd : p.getBody().getLocalVars())
			for (VarList v : vd.getVariables())
				assignments.addAll(this.prefixVarToLocalVar(v,
						parameterToVariablePrefix));

		for (VarList v : this.stack.getVariables())
			assignments.addAll(this.prefixVarToLocalVar(v,
					parameterToVariablePrefix));

		// GAMMA
		// globals
		for (VarList v : this.globalStateVars)
			assignments.addAll(this.prefixVarToLocalVar(v,
					parameterToVariablePrefix));

		return assignments.toArray(new Statement[assignments.size()]);
	}

	/**
	 * generates the variable declarations for the variables of a procedure
	 * 
	 * @param p
	 * @return
	 * 
	 *         <code>
	 * var bla : int;
	 * var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
	 * var foo : bool;
	 * </code>
	 */
	public VariableDeclaration[] cookifyArgsDeclareLocals(Procedure p,
			boolean withStack, boolean withGlobals) {
		ArrayList<VariableDeclaration> declarations = new ArrayList<VariableDeclaration>();

		// LAMBDA
		// Args (in parameters of p)
		if (p.getInParams().length > 0)
			declarations.add(new VariableDeclaration(LocationProvider
					.getLocation(), new Attribute[] {}, p.getInParams()));
		if (p.getOutParams().length > 0)
			declarations.add(new VariableDeclaration(LocationProvider
					.getLocation(), new Attribute[] {}, p.getOutParams()));
		// Locals (local variables of p)
		for (VariableDeclaration vd : p.getBody().getLocalVars()) {
			if (vd.getVariables().length > 0)
				declarations.add(new VariableDeclaration(LocationProvider
						.getLocation(), new Attribute[] {}, vd.getVariables()));
		}

		if (withStack)
			declarations.add(this.stack);

		// GAMMA
		// globals
		if (withGlobals)
			if (this.globalStateVars.length > 0)
				declarations.add(new VariableDeclaration(LocationProvider
						.getLocation(), new Attribute[] {},
						this.globalStateVars));

		return declarations
				.toArray(new VariableDeclaration[declarations.size()]);
	}

	/**
	 * append local, in, out, global, stack and pp to a parameter list for the
	 * procedure declaration parameter list: varname:type,*
	 * 
	 * @param p
	 * @return
	 * 
	 *         <code>
	 * cookiefy_args_bla:int, cookiefy_args_foo:bool, cookiefy_args_intStack:iStack, cookiefy_args_boolStack:bStack, ...
	 * </code>
	 */
	public VarList[] concatToEncParams(Procedure p) {
		ArrayList<VarList> idents = new ArrayList<VarList>();

		// LAMBDA
		// Args (in parameters of p)
		for (VarList v : p.getInParams())
			Helper.addVarListToArrayList(idents, v, parameterToVariablePrefix);
		// return
		for (VarList v : p.getOutParams())
			Helper.addVarListToArrayList(idents, v, parameterToVariablePrefix);
		// Locals (local variables of p)
		for (VariableDeclaration vd : p.getBody().getLocalVars())
			for (VarList v : vd.getVariables())
				Helper.addVarListToArrayList(idents, v,
						parameterToVariablePrefix);

		// GAMMA
		// globals
		for (VarList v : this.globalStateVars)
			Helper.addVarListToArrayList(idents, v, parameterToVariablePrefix);

		// stack
		for (VarList v : this.stack.getVariables())
			Helper.addVarListToArrayList(idents, v, parameterToVariablePrefix);

		// program counter
		idents.add(this.pp);

		return idents.toArray(new VarList[idents.size()]);
	}

	/**
	 * Parametes for procedure calls
	 * 
	 * @param p
	 * @return
	 * 
	 *         <code>
	 *  intStack, boolStack, idStack, ppStack, sp, ...
	 * </code>
	 */
	public VarList[] concatToEncParamsAtom(Procedure p) {
		ArrayList<VarList> idents = new ArrayList<VarList>();

		// LAMBDA
		// Args (in parameters of p)
		for (VarList v : p.getInParams())
			Helper.addVarListToArrayList(idents, v, "");
		// return
		for (VarList v : p.getOutParams())
			Helper.addVarListToArrayList(idents, v, "");
		// Locals (local variables of p)
		for (VariableDeclaration vd : p.getBody().getLocalVars())
			for (VarList v : vd.getVariables())
				Helper.addVarListToArrayList(idents, v, "");

		// GAMMA
		// globals
		for (VarList v : this.globalStateVars)
			Helper.addVarListToArrayList(idents, v, "");

		// stack
		for (VarList v : this.stack.getVariables())
			Helper.addVarListToArrayList(idents, v, "");

		// program counter
		idents.add(this.pp);

		return idents.toArray(new VarList[idents.size()]);
	}

	/**
	 * set the list of global variables for the function arguments
	 * 
	 * @param vd
	 */
	private void setGlobalStateVars() {
		ArrayList<VarList> vars = new ArrayList<VarList>();

		for (VariableDeclaration vdecl : InputProgram.Globals) {
			for (VarList vlist : vdecl.getVariables()) {
				Helper.addVarListToArrayList(vars, vlist, "");
			}
		}

		this.globalStateVars = vars.toArray(new VarList[vars.size()]);
	}

	/**
	 * Generates one line for cookifyArgsToVariables
	 * 
	 * @param v
	 * @param prefix
	 * @return
	 * 
	 *         <code>
	 * bla := cookiefy_args_bla;
	 * </code>
	 */
	private ArrayList<Statement> prefixVarToLocalVar(VarList v, String prefix) {
		ArrayList<Statement> assignments = new ArrayList<Statement>();
		for (String s : v.getIdentifiers())
			assignments.add(new AssignmentStatement(LocationProvider
					.getLocation(), new LeftHandSide[] { new VariableLHS(
					LocationProvider.getLocation(), s) },
					new Expression[] { new IdentifierExpression(
							LocationProvider.getLocation(), "cookiefy_args_"
									+ s) }));
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
	 *         <code>
	 * procedure enc_havoc_main_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
	 * {
	 *  var bla : int;
	 * 
	 *  havoc bla;
	 *  call ret := enc_main_T(bla, foo, intStack, boolStack, idStack, ppStack, sp, pp);
	 * }
	 * </code>
	 */
	public Procedure encodeInitProcedurestateProcedure(Procedure pPrime,
			String path, Expression[] args) {
		ArrayList<Statement> body = new ArrayList<Statement>();
		// prepare params for the havoc_... procedure
		ArrayList<VarList> params = new ArrayList<VarList>();
		for (VarList v : pPrime.getInParams())
			Helper.addVarListToArrayList(params, v,
					this.parameterToVariablePrefix);
		// globals
		for (VarList v : this.globalStateVars)
			Helper.addVarListToArrayList(params, v, "");
		for (VarList v : this.stack.getVariables())
			Helper.addVarListToArrayList(params, v, "");
		params.add(this.pp);
		// pp = 0!

		// declaration is done in the procedure declaration
		// havoc Vars
		for (VarList v : pPrime.getInParams())
			body.add(new HavocStatement(LocationProvider.getLocation(), 
					makeVariableLHS(v.getIdentifiers())));
		for (VarList v : pPrime.getOutParams())
			body.add(new HavocStatement(LocationProvider.getLocation(),
					makeVariableLHS(v.getIdentifiers())));
		for (VariableDeclaration vd : pPrime.getBody().getLocalVars())
			for (VarList v : vd.getVariables())
				body.add(new HavocStatement(LocationProvider.getLocation(),
						makeVariableLHS(v.getIdentifiers())));

		// copy arguments to vars
		for (VarList v : pPrime.getInParams())
			for (String ident : v.getIdentifiers())
				body.add(new AssignmentStatement(
						LocationProvider.getLocation(),
						new LeftHandSide[] { new VariableLHS(LocationProvider
								.getLocation(), ident) },
						new Expression[] { new IdentifierExpression(
								LocationProvider.getLocation(),
								this.parameterToVariablePrefix + ident) }));

		// call procedure
		body.add(new CallStatement(LocationProvider.getLocation(), false,
				makeVariableLHS(new String[] { "ret" }), this.methodeNameGen(pPrime, path, ""),
				this.concatToEncArgs(pPrime)));

		return new Procedure(LocationProvider.getLocation(), new Attribute[0],
				this.methodeNameGenPrepare(pPrime, path, ""), new String[0],
				params.toArray(new VarList[params.size()]),
				new VarList[] { new VarList(LocationProvider.getLocation(),
						new String[] { "ret" }, new PrimitiveType(
								LocationProvider.getLocation(), "bool")) },
				new Specification[0], new Body(LocationProvider.getLocation(),
						this.cookifyArgsDeclareLocals(pPrime, false, false),
						body.toArray(new Statement[body.size()]))

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
	private ArrayList<Statement> pushVarListToStack(VarList[] varLists) {
		ArrayList<Statement> statements = new ArrayList<Statement>();
		Expression noExp = null;
		// in parameters of p
		for (VarList v : varLists)
			for (String s : v.getIdentifiers()) {

				if (((PrimitiveType) v.getType()).getName() == "int")
					noExp = new IntegerLiteral(LocationProvider.getLocation(),
							Integer.toString(this.intStackFrameCounter));
				if (((PrimitiveType) v.getType()).getName() == "bool")
					noExp = new IntegerLiteral(LocationProvider.getLocation(),
							Integer.toString(this.boolStackFrameCounter));

				statements
						.add(new AssignmentStatement(
								LocationProvider.getLocation(),
								new LeftHandSide[] { new ArrayLHS(
										LocationProvider.getLocation(),
										new ArrayLHS(
												LocationProvider.getLocation(),
												new VariableLHS(
														LocationProvider
																.getLocation(),
														this.getStackFromType(v
																.getType())),
												new Expression[] { new IdentifierExpression(
														LocationProvider
																.getLocation(),
														"sp") }),
										new Expression[] { noExp }) },
								new Expression[] { new IdentifierExpression(
										LocationProvider.getLocation(), s) }

						));
				if (v.getType() instanceof PrimitiveType) {
					if (((PrimitiveType) v.getType()).getName() == "int")
						this.intStackFrameCounter++;
					if (((PrimitiveType) v.getType()).getName() == "bool")
						this.boolStackFrameCounter++;
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
	private ArrayList<Expression> popVarsFromStack(VarList[] varLists) {
		ArrayList<Expression> expressions = new ArrayList<Expression>();
		Expression noExp = null;
		// in parameters of p
		for (VarList v : varLists)
			for (String s : v.getIdentifiers()) {

				if (((PrimitiveType) v.getType()).getName() == "int")
					noExp = new IntegerLiteral(LocationProvider.getLocation(),
							Integer.toString(this.intStackFrameCounter));
				if (((PrimitiveType) v.getType()).getName() == "bool")
					noExp = new IntegerLiteral(LocationProvider.getLocation(),
							Integer.toString(this.boolStackFrameCounter));

				expressions.add(new ArrayAccessExpression(LocationProvider
						.getLocation(), new ArrayAccessExpression(
						LocationProvider.getLocation(),
						new IdentifierExpression(
								LocationProvider.getLocation(), this
										.getStackFromType(v.getType())),
						new Expression[] { new IdentifierExpression(
								LocationProvider.getLocation(), "sp") }),
						new Expression[] { noExp }));
				if (v.getType() instanceof PrimitiveType) {
					if (((PrimitiveType) v.getType()).getName() == "int")
						this.intStackFrameCounter++;
					if (((PrimitiveType) v.getType()).getName() == "bool")
						this.boolStackFrameCounter++;
				}

			}
		return expressions;
	}

	private String getStackFromType(ASTType type) {
		if (type instanceof PrimitiveType) {
			if (((PrimitiveType) type).getName() == "int")
				return "intStack";
			if (((PrimitiveType) type).getName() == "bool")
				return "boolStack";
		}
		return "error";
	}

	/**
	 * generates the stack push for one procedures statevars.
	 * 
	 * @param p
	 * @param pp
	 */
	public Expression[] stackPop(Procedure p) {
		ArrayList<Expression> expressions = new ArrayList<Expression>();
		// stack add
		this.intStackFrameCounter = 0;
		this.boolStackFrameCounter = 0;
		// in parameters of p
		expressions.addAll(this.popVarsFromStack(p.getInParams()));
		// out parameters of p
		expressions.addAll(this.popVarsFromStack(p.getOutParams()));
		// local variables of p

		for (VariableDeclaration vd : p.getBody().getLocalVars())
			expressions.addAll(this.popVarsFromStack(vd.getVariables()));

		// globals
		for (VarList v : this.globalStateVars)
			for (String s : v.getIdentifiers())
				expressions.add(new IdentifierExpression(LocationProvider
						.getLocation(), s));

		// stacks
		for (VarList v : this.stack.getVariables())
			for (String ident : v.getIdentifiers()) {
				if (ident == "sp")
					expressions.add(new BinaryExpression(LocationProvider
							.getLocation(),
							BinaryExpression.Operator.ARITHMINUS,
							new IdentifierExpression(LocationProvider
									.getLocation(), "sp"), new IntegerLiteral(
									LocationProvider.getLocation(), "1")));
				else
					expressions.add(new IdentifierExpression(LocationProvider
							.getLocation(), ident));

			}
		// pp
		expressions.add(new ArrayAccessExpression(LocationProvider
				.getLocation(), new IdentifierExpression(LocationProvider
				.getLocation(), "ppStack"),
				new Expression[] { new IdentifierExpression(LocationProvider
						.getLocation(), "sp") }));

		return expressions.toArray(new Expression[expressions.size()]);
	}

	/**
	 * generates the stack push for one procedures statevars.
	 * 
	 * @param p
	 * @param pp
	 */
	public ArrayList<Statement> stackPush(Procedure p, int pp) {
		this.intStackFrameCounter = 0;
		this.boolStackFrameCounter = 0;
		ArrayList<Statement> statements = new ArrayList<Statement>();
		// in parameters of p
		statements.addAll(this.pushVarListToStack(p.getInParams()));
		// out parameters of p
		statements.addAll(this.pushVarListToStack(p.getOutParams()));
		// local variables of p

		for (VariableDeclaration vd : p.getBody().getLocalVars())
			statements.addAll(this.pushVarListToStack(vd.getVariables()));

		// pp
		statements.add(new AssignmentStatement(LocationProvider.getLocation(),
				new LeftHandSide[] { new ArrayLHS(LocationProvider
						.getLocation(), new VariableLHS(LocationProvider
						.getLocation(), "ppStack"),
						new Expression[] { new IdentifierExpression(
								LocationProvider.getLocation(), "sp") }) },
				new Expression[] { new IntegerLiteral(LocationProvider
						.getLocation(), Integer.toString(pp)) }

		));
		// id
		statements.add(new AssignmentStatement(LocationProvider.getLocation(),
				new LeftHandSide[] { new ArrayLHS(LocationProvider
						.getLocation(), new VariableLHS(LocationProvider
						.getLocation(), "idStack"),
						new Expression[] { new IdentifierExpression(
								LocationProvider.getLocation(), "sp") }) },
				new Expression[] { new IntegerLiteral(LocationProvider
						.getLocation(), Integer.toString(this.identMap.getID(p
						.getIdentifier()))) }

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
	 *         <code>
	 * call ret := enc_havoc_recursive_T(0, ..., intStack, boolStack, idStack, ppStack, sp + 1, 0);
	 * </code>
	 */
	public Statement getHavocCallStatement(Expression[] args, Procedure pPrime,
			String path, Expression sp) {

		ArrayList<Expression> params = new ArrayList<Expression>();
		for (Expression e : args)
			params.add(e);

		// globals
		for (VarList v : this.globalStateVars)
			Helper.addVarListToIdentifierList(params, v);

		// stacks
		for (VarList v : this.stack.getVariables())
			for (String ident : v.getIdentifiers()) {
				if (ident == "sp")
					params.add(sp);
				else
					params.add(new IdentifierExpression(LocationProvider
							.getLocation(), ident));

			}
		// pp
		params.add(new IntegerLiteral(LocationProvider.getLocation(), "0"));

		return new CallStatement(LocationProvider.getLocation(), false,
				makeVariableLHS(new String[] { "ret" }), this.methodeNameGenPrepare(pPrime,
						path, ""),
				params.toArray(new Expression[params.size()]));

	}

	public Statement getHavocCallStatement(Expression[] args, Procedure pPrime,
			String path) {
		return getHavocCallStatement(args, pPrime, path, new BinaryExpression(
				LocationProvider.getLocation(),
				BinaryExpression.Operator.ARITHPLUS, new IdentifierExpression(
						LocationProvider.getLocation(), "sp"),
				new IntegerLiteral(LocationProvider.getLocation(), "1")));
	}

	/**
	 * creates a Call statement that calls the corresponding preturn_K function
	 * 
	 * @param path
	 * @return
	 * 
	 *         <code>
	 * call ret := preturn_T(..., intStack, boolStack, idStack, ppStack, sp);
	 * </code>
	 */
	public CallStatement pReturnCall(String path) {
		ArrayList<Expression> params = new ArrayList<Expression>();

		// globals
		for (VarList v : this.globalStateVars) {
			Helper.addVarListToIdentifierList(params, v);
		}
		// stacks
		for (VarList v : this.stack.getVariables())
			for (String ident : v.getIdentifiers()) {
				params.add(new IdentifierExpression(LocationProvider
						.getLocation(), ident));

			}

		return new CallStatement(LocationProvider.getLocation(), false,
				makeVariableLHS(new String[] { "ret" }), "preturn_" + path,
				params.toArray(new Expression[params.size()]));

	}

	/**
	 * generiter die preturn funktionen mit goto listen darin
	 * 
	 * @param path
	 * @return
	 * 
	 *         <code>
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
	public Procedure pReturn(String path) {
		ArrayList<Statement> statements = new ArrayList<Statement>();
		int pid = 0;

		statements.add(new AssignmentStatement(LocationProvider.getLocation(),
				new LeftHandSide[] { new VariableLHS(LocationProvider
						.getLocation(), "func_id") },
				new Expression[] { new ArrayAccessExpression(LocationProvider
						.getLocation(), new IdentifierExpression(
						LocationProvider.getLocation(), "idStack"),
						new Expression[] { new IdentifierExpression(
								LocationProvider.getLocation(), "sp") }) }));

		// for every procedure in the program add a sp -> procedure call
		for (String pName : this.InputProgram.Procedures.keySet()) {
			Procedure p = this.InputProgram.Procedures.get(pName);

			statements
					.add(new IfStatement(LocationProvider.getLocation(),
							new BinaryExpression(
									LocationProvider.getLocation(),
									BinaryExpression.Operator.COMPEQ,
									new IdentifierExpression(LocationProvider
											.getLocation(), "func_id"),
									new IntegerLiteral(LocationProvider
											.getLocation(), Integer
											.toString(this.identMap
													.getID(pName)))),
							new Statement[] {
							// the actual call doing the returning... wtf
							new CallStatement(LocationProvider.getLocation(),
									false, makeVariableLHS(new String[] { "ret" }), this
											.methodeNameGen(p, path, ""), this
											.stackPop(p)) }, new Statement[] {}

					));
		}

		ArrayList<VarList> idents = new ArrayList<VarList>();
		// globals
		for (VarList v : this.globalStateVars)
			Helper.addVarListToArrayList(idents, v, "");
		// stack
		for (VarList v : this.stack.getVariables())
			Helper.addVarListToArrayList(idents, v, "");
		// program counter
		// idents.add(this.pp); //Jeremi: preturn braucht keinen procedure
		// counter!

		return new Procedure(LocationProvider.getLocation(),
				new Attribute[] {}, "preturn_" + path, new String[] {},
				idents.toArray(new VarList[idents.size()]),
				new VarList[] { new VarList(LocationProvider.getLocation(),
						new String[] { "ret" }, new PrimitiveType(
								LocationProvider.getLocation(), "bool")) },
				new Specification[] {}, new Body(
						LocationProvider.getLocation(),
						new VariableDeclaration[] { new VariableDeclaration(
								LocationProvider.getLocation(),
								new Attribute[] {},
								new VarList[] { new VarList(LocationProvider
										.getLocation(),
										new String[] { "func_id" },
										new PrimitiveType(LocationProvider
												.getLocation(), "int")) }) },
						statements.toArray(new Statement[statements.size()])));
	}

}
