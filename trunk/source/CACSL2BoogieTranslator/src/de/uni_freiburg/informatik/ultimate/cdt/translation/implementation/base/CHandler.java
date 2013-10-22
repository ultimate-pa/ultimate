/**
 * The base C handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.text.ParseException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblem;
import org.eclipse.cdt.core.dom.ast.IASTProblemDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTProblemExpression;
import org.eclipse.cdt.core.dom.ast.IASTProblemStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblemTypeId;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.ArrayHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.PostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultContract;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionList;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionListRec;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Backtranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.PreferencePage;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * Class that handles translation of C nodes to Boogie nodes.
 * 
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public class CHandler implements ICHandler {
	/**
	 * Array handler.
	 */
	protected ArrayHandler arrayHandler;
	/**
	 * Function handler.
	 */
	protected FunctionHandler functionHandler;
	/**
	 * Struct handler.
	 */
	protected StructHandler structHandler;
	/**
	 * Memory handler.
	 */
	//    protected MemoryHandler memoryHandler;
	public MemoryHandler memoryHandler; //alex..
	/**
	 * Post processor.
	 */
	protected PostProcessor postProcessor;
	/**
	 * Holds the next ACSL node in the decorator tree.
	 */
	private NextACSL acsl;
	/**
	 * Contract for next procedure
	 */
	protected List<ACSLNode> contract;
	/**
	 * The symbol table for the translation.
	 */
	protected SymbolTable symbolTable;
	/**
	 * Names of all bitwise operation that occurred in the program.
	 */
	protected HashMap<String, FunctionDeclaration> functions;
	/**
	 * A set holding declarations of global variables required for variables,
	 * declared locally in C but required to be global in Boogie. e.g. constants
	 * for enums or local static variables. Each declaration can have a set of
	 * initialization statements.
	 */
	protected HashMap<Declaration, CType> globalVariables;
	/**
	 * A list of C variables for each declaration in
	 * <code>globalVariables</code>.
	 */
	protected HashMap<Declaration, ArrayList<Statement>> globalVariablesInits;
	/**
	 * A collection of axioms generated during translation process.
	 */
	protected HashSet<Axiom> axioms;

	/**
	 * Translation from Boogie to C for traces and expressions.
	 */
	protected final Backtranslator backtranslator;

	/**
	 * If set to true and the program contains an error label ULTIMATE shows
	 * a warning that suggests a different translation mode.
	 */
	protected final boolean m_ErrorLabelWarning;
	private HashSet<String> boogieIdsOfHeapVars;

	/**
	 * Constructor.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param backtranslator
	 *            a reference to the Backtranslator object.
	 */
	public CHandler(Dispatcher main, Backtranslator backtranslator, boolean errorLabelWarning) {
		this.arrayHandler = new ArrayHandler();
		this.functionHandler = new FunctionHandler();
		this.postProcessor = new PostProcessor();
		this.structHandler = new StructHandler();
		IEclipsePreferences prefs = ConfigurationScope.INSTANCE
				.getNode(Activator.s_PLUGIN_ID);
		boolean checkPointerValidity = Boolean.valueOf(
				prefs.get(PreferencePage.NAME_CHECK_POINTER_VALIDITY, "false"));
		this.memoryHandler = new MemoryHandler(checkPointerValidity);
		this.symbolTable = new SymbolTable(main);
		this.functions = new HashMap<String, FunctionDeclaration>();
		this.globalVariables = new HashMap<Declaration, CType>();
		this.globalVariablesInits = new HashMap<Declaration, ArrayList<Statement>>();
		this.axioms = new HashSet<Axiom>();
		this.backtranslator = backtranslator;
		this.contract = new ArrayList<ACSLNode>();
		this.m_ErrorLabelWarning = errorLabelWarning;
		
		this.boogieIdsOfHeapVars = new HashSet<String>();
	}

	@Override
	public Result visit(Dispatcher main, IASTNode node) {
		String errorMsg = "CHandler: Not yet implemented: \""
				+ node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		Dispatcher.error(new CACSLLocation(node),
				SyntaxErrorType.UnsupportedSyntax, errorMsg);
		throw new UnsupportedSyntaxException(errorMsg);
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Override
	public Result visit(Dispatcher main, ACSLNode node) {
		throw new UnsupportedOperationException(
				"Implementation Error: Use ACSLHandler for: " + node.getClass());
	}

	/**
	 * Checks ACSL for the next element and whether it must be added at the
	 * place where this method is called.
	 * 
	 * @param main
	 *            the main dispatcher.
	 * @param stmt
	 *            the statement list where the acsl should be appended - this is
	 *            assumed to be <code>null</code> when called from within the
	 *            <i>translation unit</i>.
	 * @param next
	 *            the current child node of a translation unit of compound
	 *            statement that will be added next. Should be <code>null</code>
	 *            when called at the end of <i>compound statement</i>.
	 * @param parent
	 *            the parent node of the current ACSL node. This should only be
	 *            set if called at the end of a <i>compound statement</i> and
	 *            <code>null</code> otherwise.
	 */
	private void checkForACSL(Dispatcher main, ArrayList<Statement> stmt,
			IASTNode next, IASTNode parent) {
		if (acsl != null) {
			if (acsl.successorCNode == null) {
				if (parent != null && stmt != null && next == null) {
					// ACSL at the end of a function
					for (ACSLNode acslNode : acsl.acsl) {
						if (parent.getFileLocation().getEndingLineNumber() <= acslNode
								.getStartingLineNumber()) {
							return; // handle later ...
						}
						Result acslResult = main.dispatch(acslNode);
						if (acslResult.node instanceof Statement) {
							if (parent.getFileLocation().getEndingLineNumber() >= acslNode
									.getEndingLineNumber()
									&& parent.getFileLocation()
									.getStartingLineNumber() <= acslNode
									.getStartingLineNumber()) {
								stmt.add((Statement) acslResult.node);
								try {
									acsl = main.nextACSLStatement();
								} catch (ParseException e1) {
									String msg = "Skipped a ACSL node due to: "
											+ e1.getMessage();
									Dispatcher.error(new CACSLLocation(parent),
											SyntaxErrorType.UnsupportedSyntax,
											msg);
								}
							}
						} else {
							String msg = "Unexpected ACSL comment: "
									+ acslResult.node.getClass();
							Dispatcher.error(new CACSLLocation(parent),
									SyntaxErrorType.IncorrectSyntax, msg);
							throw new IncorrectSyntaxException(msg);
						}
					}
				} // ELSE:
				// ACSL for next compound statement -> handle it next call
				// or in case of translation unit, ACSL in an unexpected
				// location!
			} else if (acsl.successorCNode.equals(next)) {
				assert contract.isEmpty();
				for (ACSLNode acslNode : acsl.acsl) {
					if (stmt != null) {
						// this means we are in a compound statement
						if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
							// Loop contract
							contract.add(acslNode);
						} else if (acslNode instanceof CodeAnnot) {
							Result acslResult = main.dispatch(acslNode);
							stmt.add((Statement) acslResult.node);
						} else {
							String msg = "Unexpected ACSL comment: "
									+ acslNode.getClass();
							Dispatcher.error(new CACSLLocation(next),
									SyntaxErrorType.IncorrectSyntax, msg);
							throw new IncorrectSyntaxException(msg);
						}
					} else {
						// this means we are in the translation unit
						if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
							// Function contract
							contract.add(acslNode);
						}
					}
				}
				try {
					acsl = main.nextACSLStatement();
				} catch (ParseException e1) {
					String msg = "Skipped a ACSL node due to: "
							+ e1.getMessage();
					Dispatcher.error(new CACSLLocation(parent),
							SyntaxErrorType.UnsupportedSyntax, msg);
				}
			}
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTTranslationUnit node) {
		for (IASTPreprocessorStatement preS : node
				.getAllPreprocessorStatements()) {
			Result r = main.dispatch(preS);
			if (!(r instanceof ResultSkip)) {
				throw new UnsupportedOperationException("Not yet implemented");
			}
		}
		ILocation loc = new CACSLLocation(node);
		try {
			acsl = main.nextACSLStatement();
		} catch (ParseException e1) {
			String msg = "Skipped a ACSL node due to: " + e1.getMessage();
			Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
		}
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<String> uninitGlobalVars = new ArrayList<String>();
		ArrayList<Statement> initStatements = new ArrayList<Statement>();
		for (IASTNode child : node.getChildren()) {
			checkForACSL(main, null, child, null);
			Result childRes = main.dispatch(child);
			if (childRes instanceof ResultExpression) {
				// we have to add a global variable
				ResultExpression resExp = ((ResultExpression) childRes);
				decl.addAll(resExp.decl);
				initStatements.addAll(resExp.stmt);
			} else {
				if (childRes instanceof ResultSkip)
					continue;
				assert childRes.getClass() == Result.class;
				assert childRes.node != null;
				decl.add((Declaration) childRes.node);
			}
		}
		// Collect all global variables.
		for (Declaration d : decl) {
			if (d instanceof VariableDeclaration) {
				VariableDeclaration varDecl = (VariableDeclaration) d;
				VarList[] vars = varDecl.getVariables();
				for (VarList var : vars) {
					for (String id : var.getIdentifiers()) {
						uninitGlobalVars.add(id);
					}
				}
			}
		}
		for (Statement s : initStatements) {
			if (s instanceof AssignmentStatement) {
				AssignmentStatement as = (AssignmentStatement) s;
				for (LeftHandSide lhs : as.getLhs()) {
					String varId = BoogieASTUtil.getLHSId(lhs);
					if (symbolTable.containsBoogieSymbol(varId)) {
						String cId = symbolTable.getCID4BoogieID(varId, loc);
						ASTType at = symbolTable.getTypeOfVariable(cId, loc);
						if (!(at instanceof StructType || at instanceof ArrayType)) {
							uninitGlobalVars.remove(varId);
						}
					} else {
						uninitGlobalVars.remove(varId);
					}
					// otherwise, we will init them with "0" and append the
					// given initialization later on - s.t. all global vars
					// are fully initialized!
				}
			}
		}
		for (Declaration d : globalVariables.keySet()) {
			assert d instanceof ConstDeclaration
			|| d instanceof VariableDeclaration;
			decl.add(d);
			if (d instanceof VariableDeclaration) {
				VariableDeclaration vd = (VariableDeclaration) d;
				ASTType at = vd.getVariables()[0].getType();
				if (globalVariablesInits.get(d) == null
						|| globalVariablesInits.get(d).isEmpty()
						|| at instanceof StructType || at instanceof ArrayType) {
					for (VarList vl : vd.getVariables()) {
						for (String id : vl.getIdentifiers()) {
							// if the following assert fails, we have to change
							// the name of static variables to something unique!
							// However, this should already be true, as their
							// names are scoped and should start with a tilde!
							assert !symbolTable.containsCSymbol(id);
							// the following put is a requirement of the
							// post processor. However, these variables are not
							// in this scope/"global" in the original sense of
							// the symbol table! It is assumed, that the symbol
							// table is not used for further translation steps
							// after this location!
							symbolTable.put(id, new SymbolTableValue(id, vd,
									true, globalVariables.get(d)));
							uninitGlobalVars.add(id);
						}
					}
				} else if (globalVariablesInits.get(d) != null
						&& !globalVariablesInits.get(d).isEmpty()) {
					initStatements.addAll(globalVariablesInits.get(d));
				}
			}
		}
		decl.addAll(memoryHandler.declareMemoryModelInfrastructure(main, loc));
		decl.addAll(axioms);
		if (!functionHandler.isEveryCalledProcedureDeclared()) {
			String msg = "A method was called but never declared!";
			Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
			throw new IncorrectSyntaxException(msg);
		}
		// handle proc. declaration & resolve their transitive modified globals
		decl.addAll(functionHandler.calculateTransitiveModifiesClause(main));
		decl.addAll(postProcessor.postProcess(main, loc, arrayHandler,
				initStatements, functionHandler.getProcedures(),
				functionHandler.getModifiedGlobals(),
				main.typeHandler.getUndefinedTypes(), this.functions.values(),
				uninitGlobalVars));
		return new Result(new Unit(loc, decl.toArray(new Declaration[0])));
	}

	@Override
	public Result visit(Dispatcher main, IASTFunctionDefinition node) {
		return functionHandler.handleFunctionDefinition(main, node);
	}

	/**
	 * Whether or not a new Scope should be started for this compound statement.
	 * 
	 * @param env
	 *            the environment in which the CompoundStatement is.
	 * @return whether to open a new scope in the symbol table or not.
	 */
	private static boolean isNewScopeRequired(final IASTNode env) {
		return !(env instanceof IASTForStatement)
				&& !(env instanceof IASTFunctionDefinition);
	}

	@Override
	public Result visit(Dispatcher main, IASTCompoundStatement node) {
		ILocation loc = new CACSLLocation(node);
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<VariableDeclaration> lVarDecl = new ArrayList<VariableDeclaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		IASTNode parent = node.getParent();
		if (parent instanceof IASTFunctionDefinition) {
			functionHandler.handleFunctionsInParams(main, loc, decl, stmt,
					parent);
		}
		if (isNewScopeRequired(parent))
			symbolTable.beginScope();

		for (IASTNode child : node.getChildren()) {
			checkForACSL(main, stmt, child, null);
			Result r = main.dispatch(child);
			if (r instanceof ResultExpression) {
				ResultExpression res = (ResultExpression) r;
				// assert (res.auxVars.isEmpty()) : "unhavoced auxvars";
				for (Declaration d : res.decl) {
					if (d instanceof VariableDeclaration) {
						lVarDecl.add((VariableDeclaration) d);
					}
				}
				decl.addAll(res.decl);
				stmt.addAll(res.stmt);
			}
			if (r.node != null && r.node instanceof Body) {
				// already have a unique naming for variables! --> unfold
				Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			}
		}
		checkForACSL(main, stmt, null, node);
		if (isNewScopeRequired(parent))
			symbolTable.endScope();
		return new Result(new Body(loc,
				decl.toArray(new VariableDeclaration[0]),
				stmt.toArray(new Statement[0])));
	}

	@Override
	public Result visit(Dispatcher main, IASTSimpleDeclaration node) {
		CACSLLocation loc = new CACSLLocation(node);
		if (node.getDeclSpecifier() == null) {
			String msg = "This statement can be removed!";
			Dispatcher.unsoundnessWarning(loc, msg, "empty!");
			return new ResultSkip();
		}
		/*
		 * TODO Christian: to be modified/tested
		 */
		// enum case
		if (node.getDeclSpecifier() instanceof IASTEnumerationSpecifier) {
			return handleEnumDeclaration(main, node);
		}

		Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof ResultSkip || r instanceof ResultTypes;
		if (r instanceof ResultSkip)
			return r;
		if (r instanceof ResultTypes) {
			ResultTypes resType = (ResultTypes) r;
			Map<VariableDeclaration, CACSLLocation> auxVars =
					new HashMap<VariableDeclaration, CACSLLocation>();
			Map<VariableDeclaration, CACSLLocation> emptyAuxVars =
					new HashMap<VariableDeclaration, CACSLLocation>(0);
			ResultExpression result = new ResultExpression(null, emptyAuxVars);
			ResultExpression staticVarStorage = new ResultExpression(null,
					emptyAuxVars);
			boolean isGlobal = node.getParent() == node.getTranslationUnit();
			if (isGlobal) {
				result.decl.addAll(resType.typeDeclarations);
			} else if (!resType.typeDeclarations.isEmpty()) {
				// FIXME : check if typedef can occur locally at all!
				String msg = "Unexpected location for a typedef!";
						Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
						throw new UnsupportedSyntaxException(msg);
			}

			int index = -1;
			/**
			 * Christian:
			 * C allows several declarations of "similar" types in one go.
			 * For instance:
			 * <code>int a, b[2];</code>
			 * Here <code>a</code> has type <code>int</code> and <code>b</code>
			 * has type <code>int[]</code>. To solve this, the declaration
			 * items are visited one after another.
			 */
			for (IASTDeclarator d : node.getDeclarators()) {
				++index;
				// TODO Christian: to be modified/tested
				// function case
				if (d instanceof IASTFunctionDeclarator) {
					Result rFunc = functionHandler.handleFunctionDeclaration(main,
							contract, node, index);
					assert (rFunc instanceof ResultSkip);
					// do nothing here
				}
				// array case
				else if (d instanceof IASTArrayDeclarator) {
					Result rArray = arrayHandler.handleArrayDeclaration(main,
							memoryHandler, structHandler, node, globalVariables,
							globalVariablesInits, index);
					if (rArray instanceof ResultExpression) {
						result.decl.addAll(((ResultExpression)rArray).decl);
					}
					else {
						assert (rArray instanceof ResultSkip);
						// do nothing here
					}
				}
				// standard variable case
				else {
					//true iff the declared variable will be addressoffed in the program (alex)
					boolean putOnHeap = ((MainDispatcher) main).getVariablesForHeap().contains(node);

					String cId = d.getName().getRawSignature();
					// Get the type of this variable
					assert resType.getType() != null;
					String bId = main.nameHandler.getUniqueIdentifier(node, cId,
							symbolTable.getCompoundCounter(), putOnHeap);

					if (putOnHeap)
						boogieIdsOfHeapVars.add(bId);//store it independent from the symbol table
					
					ResultTypes checkedType = checkForPointer(main,
							d.getPointerOperators(), resType);

					if (main.typeHandler.isStructDeclaration()) {
						//							if (resultCType instanceof CStruct) { //better??
						/*
						 * store C variable information into this result, as
						 * this is a struct field! We need this information to
						 * build the structs C variable information recursively.
						 */
						assert resType.cvar != null;
						result.declCTypes.add(checkedType.cvar);
					}
					ASTType type = checkedType.getType();
					
					CType cvar = checkedType.cvar;
					if (isHeapVar(bId)) {
						cvar = new CPointer(cvar);
					}
					
					VarList var = new VarList(loc, new String[] { bId }, type);
					Attribute[] attr = new Attribute[0];
					if (resType.isConst) {
						String msg = "Const declaration dropped!";
						Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax,
								msg);
					}
					VariableDeclaration decl = new VariableDeclaration(loc, attr,
							new VarList[] { var });
					symbolTable.put(cId, new SymbolTableValue(bId, decl, isGlobal,
							cvar));
					if (cvar.isStatic() && !isGlobal) {
						staticVarStorage.decl.add(decl);
					} else {
						result.decl.add(decl);
					}
					
					CType resultCType = null;
					if (cvar != null) {
						resultCType = isHeapVar(bId) ? ((CPointer)cvar).pointsToType : cvar;
						resultCType = resultCType instanceof CNamed ? 
								((CNamed) resultCType).getUnderlyingType() : 
									resultCType;
					}
					
	                // Handle initializer clause
	                if (d.getInitializer() != null) {

	                	ResultExpression rExpr = ((ResultExpression) (main
	                			.dispatch(d.getInitializer())));
	                	rExpr.cType = resultCType;
	                	rExpr = rExpr.switchToRValue(main, memoryHandler, structHandler, loc);

//	                	auxVars.putAll(rExpr.auxVars);

	                	Expression rExprExpr = null;
	                	if (resultCType instanceof CStruct) {//TODO: convertArith2.. stuff
	                		ResultExpression structCons = makeStructConstructorFromRERL(loc,
	                				(ResultExpressionListRec) rExpr, (CStruct) resultCType);
	                		rExprExpr = structCons.lrVal.getValue();
	                	} if (rExpr.cType instanceof CPointer 
	                			&& rExpr.lrVal.getValue() instanceof IntegerLiteral) {
	                		rExprExpr = ResultExpression.constructPointerFromBaseAndOffset(
	                				new IntegerLiteral(loc, new InferredType(Type.Integer), "0"),
	                				rExpr.lrVal.getValue(), loc);
	                	} else {
	                		rExprExpr = main.typeHandler.convertArith2Boolean(
	                			loc, type, rExpr.lrVal.getValue());
	                	}


	                	
	                	LRValue lrVal = isHeapVar(bId) ?
	                			new HeapLValue(new IdentifierExpression(loc, new InferredType(Type.Pointer),  bId)) :
	                				new LocalLValue(new VariableLHS(loc, new InferredType(type), bId));
	                	ResultExpression assignment = makeAssignment(main, loc, rExpr.stmt, lrVal, new RValue(rExprExpr),
	                			rExpr.decl, rExpr.auxVars, resultCType);
	                	// TODO: Ask Markus where I should havoc temp aux vars.
	                	if (resType.cvar.isStatic() && !isGlobal) {
	                		staticVarStorage.stmt.addAll(assignment.stmt);
	                		staticVarStorage.decl.addAll(assignment.decl);
	                		staticVarStorage.auxVars.putAll(assignment.auxVars);
	                		//	                            staticVarStorage.stmt.addAll(Dispatcher.createHavocsForAuxVars(auxVars));
	                	} else {
	                		result.decl.addAll(assignment.decl);
	                		result.stmt.addAll(assignment.stmt);
	                		result.auxVars.putAll(assignment.auxVars);
	                		//	                            result.stmt.addAll(Dispatcher.createHavocsForAuxVars(auxVars));
	                	}
	                	//	                    }
	                } else if (!cvar.isGlobalVariable() && !cvar.isStatic()) {
	                	/*
	                	 * if not initialized directly and if not global and not
	                	 * static. This is required, since this variable could
	                	 * be within a loop and needs to be havoc'ed to
	                	 * represent C's behavior!
	                	 */
	                	result.stmt.add(new HavocStatement(loc,
	                			new VariableLHS[] { new VariableLHS(loc, bId) }));
	                }
				}
			}
			// TODO Christian: any changes needed here?
			if (resType.cvar.isStatic() && !isGlobal) {
                assert staticVarStorage.decl.size() > 0;
                for (Declaration d : staticVarStorage.decl) {
                    globalVariables.put(d, resType.cvar);
                    assert d instanceof VariableDeclaration;
                    VariableDeclaration vd = (VariableDeclaration) d;
                    assert vd.getVariables().length == 1;
                    assert vd.getVariables()[0].getIdentifiers().length == 1;
                    String lhsId = vd.getVariables()[0].getIdentifiers()[0];
                    ArrayList<Statement> init = new ArrayList<Statement>();
                    for (ListIterator<Statement> iter = staticVarStorage.stmt
                            .listIterator(staticVarStorage.stmt.size()); iter
                            .hasPrevious();) {
                        Statement s = iter.previous();
                        assert s instanceof AssignmentStatement;
                        AssignmentStatement as = (AssignmentStatement) s;
                        assert as.getLhs().length == 1;
                        if (BoogieASTUtil.getLHSId(as.getLhs()[0])
                                .equals(lhsId)) {
                            init.add(as);
                            iter.remove();
                        }
                    }
                    globalVariablesInits.put(d, init);
                }
                assert staticVarStorage.stmt.isEmpty();
            }
            result.stmt.addAll(Dispatcher.createHavocsForAuxVars(auxVars));
            return result;
        }
        String msg = "Unknown result type: " + r.getClass();
        Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }

	private ResultExpression makeStructConstructorFromRERL(ILocation loc,
			ResultExpressionListRec rerl, CStruct structType) {
		
		if (rerl.lrVal != null) //we have an identifier (or sth else too?)
			return new ResultExpression(rerl.stmt, rerl.lrVal, rerl.decl, rerl.auxVars, rerl.cType);
		
		//everything for the new Result
		ArrayList<Statement> newStmt = new ArrayList<Statement>();
		ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		HashMap<VariableDeclaration, CACSLLocation> newAuxVars = new HashMap<VariableDeclaration, CACSLLocation>();

		String[] fieldIds = structType.getFieldIds();
		CType[] fieldTypes = structType.getFieldTypes();

		//the new Arrays for the StructConstructor
		ArrayList<String> fieldIdentifiers = new ArrayList<String>();
		ArrayList<Expression> fieldValues = new ArrayList<Expression>();

		for (int i = 0; i < fieldIds.length; i++) {
			fieldIdentifiers.add(fieldIds[i]);

			CType underlyingType;
			if (fieldTypes[i] instanceof CNamed)
				underlyingType = ((CNamed) fieldTypes[i]).getUnderlyingType();
			else
				underlyingType = fieldTypes[i];

			ResultExpression fieldRead = null; 
			if(underlyingType instanceof CPrimitive) {
				fieldRead = rerl.list.get(i);
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CPointer) {
				fieldRead = rerl.list.get(i);
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CArray) {
				throw new UnsupportedSyntaxException("..");
			} else if (underlyingType instanceof CEnum) {
				throw new UnsupportedSyntaxException("..");
			} else if (underlyingType instanceof CStruct) {
				fieldRead = makeStructConstructorFromRERL(loc, rerl.list.get(i), (CStruct) underlyingType);//todo: better location
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CNamed) {
				assert false : "This should not be the case as we took the underlying type.";
			} else {
				throw new UnsupportedSyntaxException("..");
			}	

			assert fieldRead.lrVal instanceof RValue; //should be guaranteed by readFieldInTheStructAtAddress(..)
			fieldValues.add(((RValue) fieldRead.lrVal).getValue());

		}
		StructConstructor sc = new StructConstructor(loc, 
				fieldIdentifiers.toArray(new String[0]), 
				fieldValues.toArray(new Expression[0]));

		ResultExpression result = new ResultExpression(newStmt, new RValue(sc), newDecl, newAuxVars, structType);
		return result;
	}

	@Override
    public ResultTypes checkForPointer(Dispatcher main,
            IASTPointerOperator[] pointerOps, ResultTypes resType) {
        if (pointerOps.length != 0) {
            // TODO : not sure, if this is enough!
            // There could be multiple PointerOperators (i.e.
            // IASTPointer) - what does that mean for the translation?
            // String typeId = resType.cvar.toString();
            ASTType t = MemoryHandler.POINTER_TYPE;
            CType cvar = new CPointer(resType.cvar);
            return new ResultTypes(t, resType.isConst, resType.isVoid, cvar);
        }
//        if (((MainDispatcher) main).getVariablesForHeap().contains(arg0))
        return resType;
    }

    /**
     * Handles the declaration of an enum type (-d variable).
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param node
     *            the node holding the enum declaration.
     * @return the translation of this declaration.
     */
    private Result handleEnumDeclaration(Dispatcher main,
            IASTSimpleDeclaration node) {
        Result r = main.dispatch(node.getDeclSpecifier());
        assert r instanceof ResultTypes;
        ResultTypes rt = (ResultTypes) r;
        assert rt.cvar instanceof CEnum;
        CEnum cEnum = (CEnum) rt.cvar;
        CACSLLocation loc = new CACSLLocation(node);
        String enumId = main.nameHandler.getUniqueIdentifier(node,
                cEnum.getIdentifier(), symbolTable.getCompoundCounter(), false);
        Expression oldValue = null;
        Expression[] enumDomain = new Expression[cEnum.getFieldCount()];
        for (int i = 0; i < cEnum.getFieldCount(); i++) {
            String fId = cEnum.getFieldIds()[i];
            String bId = enumId + "~" + fId;
            ResultExpression rex = null;
            if (cEnum.getFieldValue(fId) != null) {
                Result resultValue = main.dispatch(cEnum.getFieldValue(fId));
                assert resultValue instanceof ResultExpression;
                rex = (ResultExpression) resultValue;
                assert rex.stmt.isEmpty();
                assert rex.decl.isEmpty();
            }
            IType it = new InferredType(Type.Integer);
            ASTType at = new PrimitiveType(loc, it, SFO.INT);
            VarList vl = new VarList(loc, new String[] { bId }, at);
            ConstDeclaration cd = new ConstDeclaration(loc, new Attribute[0],
                    false, vl, null, false);
            globalVariables.put(cd, null);
            Expression l = new IdentifierExpression(loc, it, bId);
            Expression newValue = oldValue;
            if (oldValue == null && rex == null) {
                newValue = new IntegerLiteral(loc, SFO.NR0);
            } else if (rex == null) {
                newValue = new BinaryExpression(loc, Operator.ARITHPLUS,
                        oldValue, new IntegerLiteral(loc, SFO.NR1));
            } else {
                newValue = rex.lrVal.getValue();
            }
            oldValue = newValue;
            enumDomain[i] = newValue;
            axioms.add(new Axiom(loc, new Attribute[0], new BinaryExpression(
                    loc, Operator.COMPEQ, l, newValue)));
            symbolTable.put(fId, new SymbolTableValue(bId, cd, true, cEnum));
        }
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
        boolean isGlobal = node.getTranslationUnit() == node.getParent();
        for (IASTDeclarator d : node.getDeclarators()) {
            String cId = d.getName().getRawSignature();
            // declare an integer variable
            String bId = main.nameHandler.getUniqueIdentifier(node, cId,
                    symbolTable.getCompoundCounter(), false);
            InferredType it = new InferredType(Type.Integer);
            VarList vl = new VarList(loc, new String[] { bId },
                    new PrimitiveType(loc, it, SFO.INT));
            VariableDeclaration vd = new VariableDeclaration(loc,
                    new Attribute[0], new VarList[] { vl });
            decl.add(vd);
            symbolTable.put(cId, new SymbolTableValue(bId, vd, isGlobal, null));
            // initialize variable
            if (d.getInitializer() != null) {
                Result init = main.dispatch(d.getInitializer());
                assert init instanceof ResultExpression;
                ResultExpression i = (ResultExpression) init;
                decl.addAll(i.decl);
                stmt.addAll(i.stmt);
                VariableLHS lhs = new VariableLHS(loc, bId);
                stmt.add(new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs }, new Expression[] { i.lrVal.getValue() }));
                auxVars.putAll(i.auxVars);
            }
        }
        assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
        return new ResultExpression(stmt, null, decl, auxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTFunctionDeclarator node) {
        return functionHandler.handleFunctionDeclarator(main, node);
    }

    @Override
    public Result visit(Dispatcher main, IASTLiteralExpression node) {
        ILocation loc = new CACSLLocation(node);
        Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        switch (node.getKind()) {
            case IASTLiteralExpression.lk_float_constant:
                String val = new String(node.getValue());
                val = ISOIEC9899TC3.handleFloatConstant(val, loc);
                return new ResultExpression(new RValue(new RealLiteral(loc,
                        new InferredType(InferredType.Type.Real), val)), new CPrimitive(PRIMITIVE.FLOAT));
            case IASTLiteralExpression.lk_char_constant:
                val = new String(node.getValue());
                val = ISOIEC9899TC3.handleCharConstant(val, loc);
                assert val.length() == 3;
                assert val.startsWith("'");
                assert val.endsWith("'");
                val = SFO.EMPTY + (int) val.charAt(1);
                return new ResultExpression(new RValue(new IntegerLiteral(loc,
                        new InferredType(InferredType.Type.Integer), val)),
                        new CPrimitive(PRIMITIVE.CHAR));
            case IASTLiteralExpression.lk_integer_constant:
                val = new String(node.getValue());
                val = ISOIEC9899TC3.handleIntegerConstant(val, loc);
                return new ResultExpression(new RValue(new IntegerLiteral(loc,
                        new InferredType(InferredType.Type.Integer), val)),
                        new CPrimitive(PRIMITIVE.INT));
            case IASTLiteralExpression.lk_string_literal:
                // TODO : StringLiteral is not correct - we need a char[]...
                return new ResultExpression(new RValue(new StringLiteral(loc,
                        new InferredType(InferredType.Type.String), new String(
                                node.getValue()))), (CType) null);
            case IASTLiteralExpression.lk_false:
                return new ResultExpression(new RValue(new BooleanLiteral(loc,
                        new InferredType(InferredType.Type.Boolean), false)),
                        new CPrimitive(PRIMITIVE.BOOL));
            case IASTLiteralExpression.lk_true:
                return new ResultExpression(new RValue(new BooleanLiteral(loc,
                        new InferredType(InferredType.Type.Boolean), true)),
                        new CPrimitive(PRIMITIVE.BOOL));
            default:
                String msg = "Unknown or unsupported kind of IASTLiteralExpression";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
    }

    @Override
    public Result visit(Dispatcher main, IASTIdExpression node) {
        CACSLLocation loc = new CACSLLocation(node);
        String cId = node.getName().getRawSignature();
        ASTType astt = symbolTable.getTypeOfVariable(cId, loc);
        InferredType t = new InferredType(astt);
        String bId = symbolTable.get(cId, loc).getBoogieName();
        
        CType cT = symbolTable.get(cId, loc).getCVariable();
        
        LRValue lrVal = null;
        if (isHeapVar(bId)) {
            IdentifierExpression idExp = new IdentifierExpression(loc, t, bId);
        	lrVal = new HeapLValue(idExp);
        	cT = ((CPointer) cT).pointsToType;
        } else {
            VariableLHS idLhs = new VariableLHS(loc, t, bId);
        	lrVal = new LocalLValue(idLhs);
        }
        ResultExpression result = new ResultExpression(new ArrayList<Statement>(0),
        		lrVal, new ArrayList<Declaration>(0), new HashMap<VariableDeclaration, CACSLLocation>(0), cT);

        return result;
    }
    
    boolean isHeapVar(String boogieId) {
    	return boogieIdsOfHeapVars.contains(boogieId);
    }

//	boolean isHeapVar(Dispatcher main, CACSLLocation loc, String cId) {
//		return ((MainDispatcher) main).getBoogieDeclarationsOfVariablesOnHeapContains(
//        		(VariableDeclaration) symbolTable.get(cId, loc).getDecl());
//	}
    
    @Override
    public Result visit(Dispatcher main, IASTUnaryExpression node) {
        ResultExpression o = (ResultExpression) main
                .dispatch(node.getOperand());
        CACSLLocation loc = new CACSLLocation(node);
        InferredType tInt = new InferredType(Type.Integer);
        Expression nr1 = new IntegerLiteral(loc, tInt, SFO.NR1);
        
        //for the cases we know that it's an RValue..
        ResultExpression rop = o.switchToRValue(main, memoryHandler, structHandler, loc);
        
        switch (node.getOperator()) {
            case IASTUnaryExpression.op_minus:
                return new ResultExpression(
                		rop.stmt,
                		new RValue(new UnaryExpression(loc,
                				rop.lrVal.getValue().getType(),
                				UnaryExpression.Operator.ARITHNEGATIVE, rop.lrVal.getValue())),
                        rop.decl,
                        rop.auxVars,
                        rop.cType);
            case IASTUnaryExpression.op_not:
            	InferredType iType = (InferredType) rop.lrVal.getValue().getType();
            	/** boolean <code>p</code> becomes <code>!p ? 1 : 0</code> */
            	if (iType.getType() == InferredType.Type.Boolean) {
                    return new ResultExpression(rop.stmt,
                    		new RValue(wrapBoolean2Int(loc, new UnaryExpression(loc,
                    				UnaryExpression.Operator.LOGICNEG, rop.lrVal.getValue()))),
                    		rop.decl, rop.auxVars, rop.cType);
            	} else if (iType.getType() == InferredType.Type.Integer) {
            		// unwrap if possible
        			final Expression unwrapped =
        					main.typeHandler.unwrapInt2Boolean(rop.lrVal.getValue());
        			if (unwrapped != null) {
        				/**
        				 * int <code>x</code> of form <code>y ? 1 : 0</code>
        				 * becomes <code>!y ? 1 : 0</code>
        				 */
        				return new ResultExpression(rop.stmt,
        						new RValue(wrapBoolean2Int(loc,
        								new UnaryExpression(loc, 
        										UnaryExpression.Operator.LOGICNEG,
        										unwrapped))
        								),
        								rop.decl, 
        								rop.auxVars, 
        								rop.cType);
        			}

        			/** int <code>x</code> becomes <code>x == 0 ? 1 : 0</code> */
            		return new ResultExpression(rop.stmt,
            				new RValue(wrapBinaryBoolean2Int(loc,
            						BinaryExpression.Operator.COMPEQ, rop.lrVal.getValue(),
            						new IntegerLiteral(loc, tInt, SFO.NR0))),
            				o.decl, o.auxVars, rop.cType);
            	} else {
            		throw new UnsupportedOperationException(
            				"only bool and int at the moment");
            	}
            case IASTUnaryExpression.op_plus:
                return new ResultExpression(rop.stmt, rop.lrVal, rop.decl, rop.auxVars, rop.cType);
            case IASTUnaryExpression.op_postFixIncr:
            case IASTUnaryExpression.op_postFixDecr: {
                // E++ -> t = E; E = t + 1; t
                ArrayList<Declaration> decl = new ArrayList<Declaration>();
                ArrayList<Statement> stmt = new ArrayList<Statement>();
                Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
                // In this case we need a temporary variable
                String tmpName = main.nameHandler
                        .getTempVarUID(SFO.AUXVAR.POST_MOD);
                Expression rvalue = rop.lrVal.getValue();
                InferredType tmpIType = (InferredType) rvalue.getType();
                VariableDeclaration tmpVar = 
                		SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
                auxVars.put(tmpVar, loc);
                decl.add(tmpVar);
                stmt.addAll(rop.stmt);
                decl.addAll(rop.decl);
                stmt.add(new AssignmentStatement(loc,
                        new LeftHandSide[] { new VariableLHS(loc, tmpIType,
                                tmpName) }, new Expression[] { rvalue}));
                RValue tmpRValue = new RValue(new IdentifierExpression(loc, tmpIType, tmpName));
                int op;
                if (node.getOperator() == IASTUnaryExpression.op_prefixIncr) 
                    op = IASTBinaryExpression.op_plus;
                else 
                    op = IASTBinaryExpression.op_minus;
                                Expression rhs = null;
                if (o.cType instanceof CPointer)
            		rhs = doPointerArith(main, op,
            				loc,
            				tmpRValue.getValue(),
							nr1);
//							.lrVal.getValue();
                else
                	rhs = createArithmeticExpression(op, tmpRValue.getValue(), nr1, loc);
                
                assert !(o.lrVal instanceof RValue);
                ResultExpression assign = makeAssignment(main, loc, stmt, o.lrVal, 
                		new RValue(rhs), decl, auxVars, o.cType);
                return new ResultExpression(assign.stmt, tmpRValue, 
                		assign.decl, assign.auxVars, assign.cType);
            }
            case IASTUnaryExpression.op_prefixDecr:
            case IASTUnaryExpression.op_prefixIncr: {
                // ++E -> t = E+1; E = t; t
                ArrayList<Declaration> decl = new ArrayList<Declaration>();
                ArrayList<Statement> stmt = new ArrayList<Statement>();
                Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
                // In this case we need a temporary variable
                String tmpName = main.nameHandler
                        .getTempVarUID(SFO.AUXVAR.POST_MOD);
                Expression rvalue = rop.lrVal.getValue();
                InferredType tmpIType = (InferredType) rvalue.getType();
                VariableDeclaration tmpVar = 
                		SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
                auxVars.put(tmpVar, loc);
                decl.add(tmpVar);
                stmt.addAll(rop.stmt);
                decl.addAll(rop.decl);
                int op;
                if (node.getOperator() == IASTUnaryExpression.op_prefixIncr) 
                    op = IASTBinaryExpression.op_plus;
                else 
                    op = IASTBinaryExpression.op_minus;
                    
                Expression rhs = null;
                if (o.cType instanceof CPointer)
            		rhs = doPointerArith(main, op,  
            				 loc, o.lrVal.getValue(),
							nr1);
//							.lrVal.getValue();
                else
                	rhs = createArithmeticExpression(op, rvalue, nr1, loc);
                	
                stmt.add(new AssignmentStatement(loc,
                        new LeftHandSide[] { new VariableLHS(loc, tmpIType,
                                tmpName) }, new Expression[] { rhs }));
                assert !(o.lrVal instanceof RValue);
                RValue tmpRValue = new RValue(new IdentifierExpression(loc, tmpIType, tmpName));
                ResultExpression assign = makeAssignment(main, loc, stmt, o.lrVal, tmpRValue, decl, auxVars, o.cType);
                return new ResultExpression(assign.stmt, tmpRValue, 
                		assign.decl, assign.auxVars, assign.cType);
            }
            case IASTUnaryExpression.op_bracketedPrimary:
                return o;
            case IASTUnaryExpression.op_sizeof:
                Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                        0);
                return new ResultExpression(new RValue(memoryHandler.getSizeOf(main,
                        node.getOperand())), emptyAuxVars);
            case IASTUnaryExpression.op_star:
            {
            	assert rop.cType instanceof CPointer : "type error: expected pointer , got " + rop.cType.toString();
                Expression addr = rop.lrVal.getValue();
                return new ResultExpression(rop.stmt, new HeapLValue(addr), rop.decl, 
                		rop.auxVars, ((CPointer)rop.cType).pointsToType);
            }
//                // Expression access = new ArrayAccessExpression(loc,
//                // new IdentifierExpression(loc, SFO.MEMORY),
//                // new Expression[] { idx });
//                if (!(idx instanceof IdentifierExpression)) {
//                    String msg = "Pointers on non primitive types not yet supported!";
//                    Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax,
//                            msg);
//                    throw new UnsupportedSyntaxException(msg);
//                }
//                CType cvar;
//                if (o instanceof ResultExpressionPointerDereference) {
//                	// if parent is field dereference we get the cvar from the
//                	// result expression
//                	cvar = o.cType;
//                	assert (cvar instanceof CPointer);
//                } else {
//                	String cId = symbolTable.getCID4BoogieID(
//                        ((IdentifierExpression) idx).getIdentifier(), loc);
//                	cvar = symbolTable.get(cId, loc).getCVariable();
//                }
//                if (!(cvar instanceof CPointer)) {
//                    String msg = "Type error!";
//                    Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax,
//                            msg);
//                    throw new UnsupportedSyntaxException(msg);
//                }
//                cvar = ((CPointer) cvar).pointsToType;
//                if (!(cvar instanceof CPrimitive)) {
//                	ResultExpression rex = new ResultExpressionPointerDereference(
//                			o.stmt, null, o.decl, o.auxVars, o.expr, null, null);
//                	rex.cType = cvar;
//                	return rex;
//                }
//                InferredType t = tInt;
//                switch ((((CPrimitive) cvar)).getType()) {
//                    case BOOL:
//                        t = tBool;
//                        break;
//                    case FLOAT:
//                        t = new InferredType(Type.Real);
//                        break;
////                    case POINTER:
////                        t = new InferredType(Type.Pointer);
////                        break;
//                    default:
//                }
//                ResultExpressionPointerDereference repd = 
//                		memoryHandler.getReadCall(main, t, idx);
//                ResultExpression rex = repd;
//                rex.stmt.addAll(o.stmt);
//                rex.decl.addAll(o.decl);
//                rex.auxVars.putAll(o.auxVars);
//                rex.cType = cvar;
//                return rex;
            case IASTUnaryExpression.op_amper:
            	if (o.lrVal instanceof HeapLValue) {
                    Expression addr = ((HeapLValue)o.lrVal).getAddress();
                    return new ResultExpression(o.stmt, new RValue(addr), o.decl, 
                    		o.auxVars, new CPointer(o.cType));
            	} else {
            		throw new AssertionError("Address of something that is not on the heap.");
            	}
            case IASTUnaryExpression.op_alignOf:
            case IASTUnaryExpression.op_tilde:
            default:
                String msg = "Unknown or unsupported unary operation: "
                        + node.getOperator();
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
    }

    private ResultExpression makeAssignment(Dispatcher main, ILocation loc, ArrayList<Statement> stmt,
			LRValue lrVal, RValue rVal, ArrayList<Declaration> decl,
			Map<VariableDeclaration, CACSLLocation> auxVars, CType cType) {
    	
    	RValue rightHandSide = rVal;

    	
    	if (lrVal instanceof HeapLValue) {
        	// case where left hand side is dereferenced pointer
    		HeapLValue repdL = (HeapLValue) lrVal; 
       		ResultExpression rex = memoryHandler.getWriteCall(repdL.getAddress(), rightHandSide.getValue());
    		
    		stmt.addAll(rex.stmt);
    		decl.addAll(rex.decl);
    		auxVars.putAll(rex.auxVars);
//    		addHeapModifiedGlobals(); //method unneccessary if only called here..
    		for (String t : new String[] { SFO.INT, SFO.POINTER,
    				SFO.REAL, SFO.BOOL }) {
    			functionHandler.getModifiedGlobals()
    			.get(functionHandler.getCurrentProcedureID())
    			.add(SFO.MEMORY + "_" + t);
    		}
    		return new ResultExpression(stmt, rightHandSide, decl, auxVars, cType);
    	} else if (lrVal instanceof LocalLValue){
    		LocalLValue lValue = (LocalLValue) lrVal;
    		stmt.add(new AssignmentStatement(loc, new LeftHandSide[]{lValue.getLHS()}, 
    				new Expression[] {rightHandSide.getValue()}));
    		
    		if (!functionHandler.noCurrentProcedure())
    			functionHandler.checkIfModifiedGlobal(main,
    					BoogieASTUtil.getLHSId(lValue.getLHS()), loc);
    		return new ResultExpression(stmt, new RValue(lValue.getValue()), decl, auxVars, cType);
    	} else
    		throw new AssertionError("Type error: trying to assign to an RValue in Statement" + loc.toString());
	}

	@Override
    public Result visit(Dispatcher main, IASTBinaryExpression node) {
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
        CACSLLocation loc = new CACSLLocation(node);

        ResultExpression l = (ResultExpression) main.dispatch(node
                .getOperand1());
        ResultExpression r = (ResultExpression) main.dispatch(node
                .getOperand2());

//        assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";

        InferredType tInt = new InferredType(InferredType.Type.Integer);
    	ResultExpression rl = l.switchToRValue(main, memoryHandler, structHandler, loc);
    	ResultExpression rr = r.switchToRValue(main, memoryHandler, structHandler, loc);
    	
    	// for implicit casts of Integers to Pointers
    	RValue rlRValAsPointer = new RValue(new StructConstructor(loc, new InferredType(Type.Pointer), 
    			new String[]{"base", "offset"}, new Expression[]{
    		new IntegerLiteral(loc, new InferredType(Type.Integer), "0"), 
    		rl.lrVal.getValue()}));
    	
    	RValue rrRValAsPointer = new RValue(new StructConstructor(loc, new InferredType(Type.Pointer), 
    				new String[]{"base", "offset"}, new Expression[]{
    		    			new IntegerLiteral(loc, new InferredType(Type.Integer), "0"), 
    		    			rr.lrVal.getValue()}));
    	

        switch (node.getOperator()) {
            case IASTBinaryExpression.op_assign: {
            	RValue rightSide = (RValue) rr.lrVal;
            	if (l.cType instanceof CPointer 
            			&& rr.cType instanceof CPrimitive
            			&& ((CPrimitive) rr.cType).getType() == PRIMITIVE.INT) 
            		rightSide = rrRValAsPointer;

            	stmt.addAll(l.stmt);
            	stmt.addAll(rr.stmt);
            	decl.addAll(l.decl);
            	decl.addAll(rr.decl);
            	auxVars.putAll(l.auxVars);
            	auxVars.putAll(rr.auxVars);
            	ResultExpression rex = makeAssignment(main, loc, stmt, l.lrVal, rightSide, decl, auxVars, r.cType);
                return rex;
            }
            case IASTBinaryExpression.op_equals:
            case IASTBinaryExpression.op_greaterEqual:
            case IASTBinaryExpression.op_greaterThan:
            case IASTBinaryExpression.op_lessEqual:
            case IASTBinaryExpression.op_lessThan:
            case IASTBinaryExpression.op_notequals:
            {
            	BinaryExpression.Operator op;
            	switch (node.getOperator()) {
                case IASTBinaryExpression.op_equals:
                	op = BinaryExpression.Operator.COMPEQ;
                	break;
                case IASTBinaryExpression.op_greaterEqual:
                	op = BinaryExpression.Operator.COMPGEQ;
                	break;
                case IASTBinaryExpression.op_greaterThan:
                	op = BinaryExpression.Operator.COMPGT;
                	break;
                case IASTBinaryExpression.op_lessEqual:
                	op = BinaryExpression.Operator.COMPLEQ;
                	break;
                case IASTBinaryExpression.op_lessThan:
                	op = BinaryExpression.Operator.COMPLT;
                	break;
                case IASTBinaryExpression.op_notequals:
                	op = BinaryExpression.Operator.COMPNEQ;
                	break;
                default:
                	throw new AssertionError("???");
            	}
            	stmt.addAll(rl.stmt);
                stmt.addAll(rr.stmt);
                decl.addAll(rl.decl);
            	decl.addAll(rr.decl);
            	auxVars.putAll(rl.auxVars);
            	auxVars.putAll(rr.auxVars);
            	
                Expression expr = null;
            	if (rl.cType instanceof CPointer
            			&& rr.cType instanceof CPrimitive
            			&& ((CPrimitive) rr.cType).getType() == PRIMITIVE.INT) {
            		expr = new BinaryExpression(loc, new InferredType(Type.Boolean), op, rl.lrVal.getValue(), rrRValAsPointer.getValue());
            	} else if (rr.cType instanceof CPointer
            			&& rl.cType instanceof CPrimitive
            			&& ((CPrimitive) rl.cType).getType() == PRIMITIVE.INT) {
            		expr = new BinaryExpression(loc, new InferredType(Type.Boolean), op, rlRValAsPointer.getValue(), rr.lrVal.getValue());
            	} else {
            		expr = wrapBinaryBoolean2Int(loc, op, 
            				rl.lrVal.getValue(), rr.lrVal.getValue());
            	}
                return new ResultExpression(stmt, new RValue(expr), decl, auxVars);
            }
            case IASTBinaryExpression.op_logicalAnd: {
                stmt.addAll(rl.stmt);
                stmt.addAll(rr.stmt);
                decl.addAll(rl.decl);
            	decl.addAll(rr.decl);
            	auxVars.putAll(rl.auxVars);
            	auxVars.putAll(rr.auxVars);
            	
                if (rr.stmt.isEmpty()) {
                	// no statements in right operands, hence no side effects in operand
                	// we can directly combine operands with LOGICAND
                	Expression lBool = main.typeHandler.convertArith2Boolean(
						loc, new PrimitiveType(loc, SFO.BOOL),
						rl.lrVal.getValue());
                	Expression rBool = main.typeHandler.convertArith2Boolean(
						loc, new PrimitiveType(loc, SFO.BOOL),
						rr.lrVal.getValue());
                	return new ResultExpression(stmt, 
                			new RValue(wrapBinaryBoolean2Int(loc,
                					BinaryExpression.Operator.LOGICAND,
                					lBool, rBool)),
                			decl, auxVars, new CPrimitive(CPrimitive.PRIMITIVE.INT));
                }
                // create and add tmp var #t~AND~UID
                String resName = main.nameHandler
                        .getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT);
                VarList tempVar = new VarList(loc, new String[] { resName },
                        new PrimitiveType(loc, SFO.INT));
                VariableDeclaration tmpVar = new VariableDeclaration(loc,
                        new Attribute[0], new VarList[] { tempVar });
                auxVars.put(tmpVar, loc);
                decl.add(tmpVar);
                VariableLHS lhs = new VariableLHS(loc, tInt, resName);
                Expression tmpRval = new IdentifierExpression(loc, tInt, resName);
                tmpRval = main.typeHandler.convertArith2Boolean(loc,
                				new PrimitiveType(loc, SFO.BOOL),
                				tmpRval);
                // #t~AND~UID = left
                AssignmentStatement aStat = new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs }, new Expression[] { rl.lrVal.getValue() });
                stmt.add(aStat);
                // if (#t~AND~UID) {#t~AND~UID = right;}
                ArrayList<Statement> outerThenPart = new ArrayList<Statement>();
                outerThenPart.addAll(rr.stmt);
                outerThenPart.add(new AssignmentStatement(loc,
                                new LeftHandSide[] { lhs }, new Expression[] { rr.lrVal.getValue() }));
                IfStatement ifStatement = new IfStatement(loc, tmpRval,
                        outerThenPart.toArray(new Statement[0]),
                        new Statement[0]);
                stmt.add(ifStatement);
                return new ResultExpression(stmt,
                		new RValue(tmpRval),
        				decl, auxVars, new CPrimitive(CPrimitive.PRIMITIVE.INT));
            }
            case IASTBinaryExpression.op_logicalOr: {
                stmt.addAll(rl.stmt);
                stmt.addAll(rr.stmt);
                decl.addAll(rl.decl);
            	decl.addAll(rr.decl);
            	auxVars.putAll(rl.auxVars);
            	auxVars.putAll(rr.auxVars);
            	
                if (rr.stmt.isEmpty()) {
                	Expression lBool = main.typeHandler.convertArith2Boolean(
						loc, new PrimitiveType(loc, SFO.BOOL),
						rl.lrVal.getValue());
                	Expression rBool = main.typeHandler.convertArith2Boolean(
						loc, new PrimitiveType(loc, SFO.BOOL),
						rr.lrVal.getValue());
                	// no auxVar in operands, hence no side effects in operands
                	// we can directly combine operands with LOGICOR
                	return new ResultExpression(stmt,
                			new RValue(wrapBinaryBoolean2Int(loc,
                					BinaryExpression.Operator.LOGICOR,
                					lBool, rBool)),
                			decl, auxVars, new CPrimitive(CPrimitive.PRIMITIVE.INT));
                }
                // create and add tmp var #t~OR~UID
                String resName = main.nameHandler
                        .getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT);
                VarList tempVar = new VarList(loc, new String[] { resName },
                        new PrimitiveType(loc, SFO.INT));
                VariableDeclaration tmpVar = new VariableDeclaration(loc,
                        new Attribute[0], new VarList[] { tempVar });
                auxVars.put(tmpVar, loc);
                decl.add(tmpVar);
                VariableLHS lhs = new VariableLHS(loc, tInt, resName);
                Expression tmpRval = new IdentifierExpression(loc, tInt, resName);
                tmpRval = main.typeHandler.convertArith2Boolean(loc,
                				new PrimitiveType(loc, SFO.BOOL),
                				tmpRval);
                // #t~OR~UID = left
                AssignmentStatement aStat = new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs }, new Expression[] { rl.lrVal.getValue() });
                stmt.add(aStat);
                // if (#t~OR~UID) {} else {#t~OR~UID = right;}
                ArrayList<Statement> outerElsePart = new ArrayList<Statement>();
                outerElsePart.addAll(rr.stmt);
                outerElsePart.add(new AssignmentStatement(loc,
                                new LeftHandSide[] { lhs }, new Expression[] { rr.lrVal.getValue() }));
                IfStatement ifStatement = new IfStatement(loc, tmpRval,
                		new Statement[0], outerElsePart.toArray(new Statement[0]));
                stmt.add(ifStatement);
                return new ResultExpression(stmt,
                		new RValue(tmpRval),
            			decl, auxVars, new CPrimitive(CPrimitive.PRIMITIVE.INT));
            }
            case IASTBinaryExpression.op_minus:
            case IASTBinaryExpression.op_plus:
            case IASTBinaryExpression.op_modulo:
            case IASTBinaryExpression.op_multiply:
            case IASTBinaryExpression.op_divide: {
            	stmt.addAll(rl.stmt);
                stmt.addAll(rr.stmt);
                decl.addAll(rl.decl);
                decl.addAll(rr.decl);
                auxVars.putAll(rl.auxVars);
                auxVars.putAll(rr.auxVars);
                
                if (node.getOperator() == IASTBinaryExpression.op_divide) {
                    CACSLLocation assertLoc = new CACSLLocation(node,
                            new Check(Check.Spec.DIVISION_BY_ZERO));
                    stmt.add(new AssertStatement(assertLoc,
                            new BinaryExpression(assertLoc,
                                    BinaryExpression.Operator.COMPNEQ,
                                    new IntegerLiteral(assertLoc, SFO.NR0),
                                    rr.lrVal.getValue())));
                }
                
                Expression expr = null;
            	if (rl.cType instanceof CPointer
            			&& rr.cType instanceof CPrimitive
            			&& ((CPrimitive) rr.cType).getType() == PRIMITIVE.INT) {
            		expr = doPointerArith(main, node.getOperator(), 
            				loc, rl.lrVal.getValue(), rr.lrVal.getValue());
            	} else if (rr.cType instanceof CPointer
            			&& rl.cType instanceof CPrimitive
            			&& ((CPrimitive) rl.cType).getType() == PRIMITIVE.INT) {
            		expr = doPointerArith(main, node.getOperator(), loc, rr.lrVal.getValue(),
							rl.lrVal.getValue());
            	} else {
            		expr = createArithmeticExpression(
            				node.getOperator(), rl.lrVal.getValue(), rr.lrVal.getValue(), loc);
            	}
                assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                return new ResultExpression(stmt, new RValue(expr), decl, auxVars, rl.cType);
            }
            case IASTBinaryExpression.op_minusAssign:
            case IASTBinaryExpression.op_multiplyAssign:
            case IASTBinaryExpression.op_divideAssign:
            case IASTBinaryExpression.op_moduloAssign:
            case IASTBinaryExpression.op_plusAssign: {
                stmt.addAll(rl.stmt);
                stmt.addAll(rr.stmt);
                decl.addAll(rl.decl);
                decl.addAll(rr.decl);
                auxVars.putAll(rl.auxVars);
                auxVars.putAll(rr.auxVars);
                
                if (node.getOperator() == IASTBinaryExpression.op_divideAssign) {
                    CACSLLocation assertLoc = new CACSLLocation(node,
                            new Check(Check.Spec.DIVISION_BY_ZERO));
                    stmt.add(new AssertStatement(assertLoc,
                            new BinaryExpression(assertLoc,
                                    BinaryExpression.Operator.COMPNEQ,
                                    new IntegerLiteral(assertLoc, SFO.NR0),
                                    rr.lrVal.getValue())));
                }
                // handle pointer arithmetic.
                Expression rightHandside = null;
                if (rl.cType instanceof CPointer
            			&& rr.cType instanceof CPrimitive
            			&& ((CPrimitive) rr.cType).getType() == PRIMITIVE.INT) {
//                	if (node.getOperator() != IASTBinaryExpression.op_plusAssign
//                			&& node.getOperator() != IASTBinaryExpression.op_minusAssign)
//                		throw new AssertionError("Type Error: trying to do pointer arithmetic" +
//                				"with some other operator than + or -");
            		rightHandside = doPointerArith(main, node.getOperator(), 
            				loc, rl.lrVal.getValue(), rr.lrVal.getValue());
            	} else {
            		rightHandside = createArithmeticExpression(node.getOperator(),
                		rl.lrVal.getValue(), rr.lrVal.getValue(), loc);
            	}
                return makeAssignment(main, loc, stmt, l.lrVal, new RValue(rightHandside), 
                		decl, auxVars, l.cType);
            }
            case IASTBinaryExpression.op_binaryAnd:
            case IASTBinaryExpression.op_binaryOr:
            case IASTBinaryExpression.op_binaryXor:
            case IASTBinaryExpression.op_shiftLeft:
            case IASTBinaryExpression.op_shiftRight: {
                stmt.addAll(rl.stmt);
                stmt.addAll(rr.stmt);
                decl.addAll(rl.decl);
                decl.addAll(rr.decl);
                auxVars.putAll(rl.auxVars);
                auxVars.putAll(rr.auxVars);
                Expression bwexpr = createBitwiseExpression(node.getOperator(),
                		rl.lrVal.getValue(), rr.lrVal.getValue(), loc);
                return new ResultExpression(stmt, new RValue(bwexpr), decl, auxVars, rl.cType);
            }
            case IASTBinaryExpression.op_shiftLeftAssign:
            case IASTBinaryExpression.op_shiftRightAssign:
                // return main.sideEffectHandler.visit(main, node);
            case IASTBinaryExpression.op_binaryAndAssign:
            case IASTBinaryExpression.op_binaryOrAssign:
            case IASTBinaryExpression.op_binaryXorAssign: {
                stmt.addAll(rl.stmt);
                stmt.addAll(rr.stmt);
                decl.addAll(rl.decl);
                decl.addAll(rr.decl);
                auxVars.putAll(rl.auxVars);
                auxVars.putAll(rr.auxVars);
                Expression bwexpr = createBitwiseExpression(
                        node.getOperator(), rl.lrVal.getValue(), rr.lrVal.getValue(), loc);
                return makeAssignment(main, loc, stmt, l.lrVal, new RValue(bwexpr), decl, auxVars, l.cType);
            }
            default:
                String msg = "Unknown or unsupported unary operation";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
    }

	private Expression doPointerArith(Dispatcher main, int operator,
//			ArrayList<Declaration> decl, ArrayList<Statement> stmt,
//			Map<VariableDeclaration, CACSLLocation> auxVars, 
			CACSLLocation loc,
			Expression ptrRex, Expression intRex) {
//		assert operator == IASTBinaryExpression.op_plus 
//				|| operator == IASTBinaryExpression.op_minus : "Trying pointer arithmetic with wrong operator";
		Expression pointerOffset = ResultExpression.getPointerOffset(ptrRex, loc);
		Expression sum = createArithmeticExpression(
		    operator, pointerOffset, intRex, loc);
		Expression pointerBase = ResultExpression.getPointerBaseAddress(ptrRex, loc);
		StructConstructor newPointer = ResultExpression.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
//		assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
//		return new ResultExpression(stmt, new RValue(newPointer), decl, auxVars,
//				ptrRex.cType);//FIXME (in fact we don't know the exact pointer type, right?)
		return newPointer;
	}
    
    /**
     * Transform an int expression to a pointer. The base address of the 
     * resulting pointer is 0,  the int expression becomes the offset of the pointer.
     */
    private ResultExpression getPointerFromInt(Dispatcher main, CACSLLocation loc, Expression intExpr) { 
    	assert ((InferredType) intExpr.getType()).getType().equals(Type.Integer);
    	Expression zero = new IntegerLiteral(loc, SFO.NR0);
    	ResultExpression auxPointer = memoryHandler.auxiliaryPointer(main, loc, zero, intExpr); 
    	return auxPointer;
    }
    
    /**
     * Given the cvar of a left hand side and the expression of a right hand
     * side (of an equality). Return true if lhs is a Pointer and the rhs is an
     * int.
     */
    private boolean cTypeIsPointerAndExpressionIsInt(CType cvar, Expression rhs) {
    	if (cvar instanceof CNamed) { 
    		cvar = ((CNamed) cvar).getMappedType();
    	}
    	if (cvar instanceof CPointer) {
        	InferredType it = (InferredType) rhs.getType();
        	return it.getType().equals(Type.Integer);
    	} else {
    		return false;
    	}
    }

    /**
     * Translates arithmetic binary expressions.
     * 
     * @param op
     *            the IASTBinaryExpression.Operator
     * @param left
     *            the left part of the expression
     * @param right
     *            the right part of the expression
     * @param loc
     *            the location of the translated node
     * @return the resulting binary expres
     */
    Expression createArithmeticExpression(int op,
            Expression left, Expression right, CACSLLocation loc) {
        BinaryExpression.Operator operator;
        switch (op) {
            case IASTBinaryExpression.op_minusAssign:
            case IASTBinaryExpression.op_minus:
                operator = Operator.ARITHMINUS;
                break;
            case IASTBinaryExpression.op_multiplyAssign:
            case IASTBinaryExpression.op_multiply:
                operator = Operator.ARITHMUL;
                break;
            case IASTBinaryExpression.op_divideAssign:
            case IASTBinaryExpression.op_divide:
                operator = Operator.ARITHDIV;
                break;
            case IASTBinaryExpression.op_moduloAssign:
            case IASTBinaryExpression.op_modulo:
                operator = Operator.ARITHMOD;
                break;
            case IASTBinaryExpression.op_plusAssign:
            case IASTBinaryExpression.op_plus:
                operator = Operator.ARITHPLUS;
                break;
//            case IASTBinaryExpression.op_equals:
//            	operator = Operator.COMPEQ;
//            	break;
//            case IASTBinaryExpression.op_notequals:
//            	operator = Operator.COMPNEQ;
//            	break;
            default:
                String msg = "Unknown or unsupported arithmetic expression";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }

        // Infer type of this expression
        InferredType t = new InferredType(InferredType.Type.Unknown);
        if (left.getType() != null && right.getType() != null
                && left.getType() instanceof InferredType
                && right.getType() instanceof InferredType) {
            InferredType lt = (InferredType) left.getType();
            InferredType rt = (InferredType) right.getType();
            if (lt.getType() == InferredType.Type.Boolean
                    || rt.getType() == InferredType.Type.Boolean) {
                String msg = "Arithmetic operation over bools - don't know how to handle that!";
                Dispatcher.error(loc, SyntaxErrorType.TypeError, msg);
                throw new UnsupportedSyntaxException(msg);
            } else if (lt.getType() == InferredType.Type.Real
                    || rt.getType() == InferredType.Type.Real) {
                t = new InferredType(InferredType.Type.Real);
            } else if (lt.getType() == InferredType.Type.Integer
                    && rt.getType() == InferredType.Type.Integer) {
                t = new InferredType(InferredType.Type.Integer);
            }
        }

        return new BinaryExpression(loc, t, operator, left, right);
    }

    /**
     * Translates bitwise binary expressions.
     * 
     * @param op
     *            the IASTBinaryExpression.Operator
     * @param left
     *            the left part of the expression
     * @param right
     *            the right part of the expression
     * @param loc
     *            the location of the translated node
     * @return the resulting binary expression
     */
    private Expression createBitwiseExpression(int op, Expression left,
            Expression right, CACSLLocation loc) {
        String operatorName;
        switch (op) {
            case IASTBinaryExpression.op_binaryAnd:
            case IASTBinaryExpression.op_binaryAndAssign:
                operatorName = "bitwiseAnd";
                break;
            case IASTBinaryExpression.op_binaryOr:
            case IASTBinaryExpression.op_binaryOrAssign:
                operatorName = "bitwiseOr";
                break;
            case IASTBinaryExpression.op_binaryXor:
            case IASTBinaryExpression.op_binaryXorAssign:
                operatorName = "bitwiseXor";
                break;
            case IASTBinaryExpression.op_shiftLeft:
            case IASTBinaryExpression.op_shiftLeftAssign:
                operatorName = "shiftLeft";
                break;
            case IASTBinaryExpression.op_shiftRight:
            case IASTBinaryExpression.op_shiftRightAssign:
                operatorName = "shiftRight";
                break;
            default:
                String msg = "Unknown or unsupported arithmetic expression";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
        InferredType lt = (InferredType) left.getType();
        InferredType rt = (InferredType) right.getType();
        if (lt.getType() != InferredType.Type.Integer
                || rt.getType() != InferredType.Type.Integer) {
            String msg = "Operands of bitwise operators have to have type int";
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        if (!this.functions.containsKey(operatorName)) {
            ASTType intType = new PrimitiveType(loc, SFO.INT);
            VarList a = new VarList(loc, new String[] { "a" }, intType);
            VarList b = new VarList(loc, new String[] { "b" }, intType);
            VarList out = new VarList(loc, new String[] { "out" }, intType);
            FunctionDeclaration d = new FunctionDeclaration(loc,
                    new Attribute[0], "~" + operatorName, new String[0],
                    new VarList[] { a, b }, out);
            this.functions.put(operatorName, d);
        }
        Expression[] arguments = { left, right };
        InferredType resultType = new InferredType(InferredType.Type.Integer);
        return new FunctionApplication(loc, resultType, "~" + operatorName,
                arguments);
    }

    @Override
    public Result visit(Dispatcher main, IASTEqualsInitializer node) {
        return main.dispatch(node.getInitializerClause());
    }

    @Override
    public Result visit(Dispatcher main, IASTDeclarationStatement node) {
        return main.dispatch(node.getDeclaration());
    }

    @Override
    public Result visit(Dispatcher main, IASTReturnStatement node) {
        return functionHandler.handleReturnStatement(main, memoryHandler, structHandler, node);
    }

    @Override
    public Result visit(Dispatcher main, IASTExpressionStatement node) {
        Result r = main.dispatch(node.getExpression());
        if (r instanceof ResultExpression) {
            ResultExpression res = (ResultExpression) r;
            if (!res.stmt.isEmpty()) {
                ResultExpression rExp = (ResultExpression) r;
                ArrayList<Statement> stmt = new ArrayList<Statement>(rExp.stmt);
                ArrayList<Declaration> decl = new ArrayList<Declaration>(
                        rExp.decl);
                assert (main.isAuxVarMapcomplete(decl, rExp.auxVars));
                Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                        0);
                return new ResultExpression(stmt, null, decl, emptyAuxVars);
            } else {
                Dispatcher.unsoundnessWarning(new CACSLLocation(node),
                        "This statement has no effect and will be dropped: "
                                + node.getRawSignature(),
                        "This statement has no effect!");
                return new ResultSkip();
            }
        } else if (r instanceof ResultExpressionList) {
            ArrayList<Statement> stmt = new ArrayList<Statement>();
            ArrayList<Declaration> decl = new ArrayList<Declaration>();
            for (ResultExpression res : ((ResultExpressionList) r).list) {
                if (!res.stmt.isEmpty()) {
                    stmt.addAll(res.stmt);
                    decl.addAll(res.decl);
                    assert (main.isAuxVarMapcomplete(res.decl, res.auxVars));
                    stmt.addAll(Dispatcher.createHavocsForAuxVars(res.auxVars));
                }
            }
            Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                    0);
            return new ResultExpression(stmt, null, decl, emptyAuxVars);
        } else if (r instanceof ResultSkip) {
            return r;
        }
        String msg = "We always convert to AssignmentStatement, other options raise this error!";
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTIfStatement node) {
        CACSLLocation loc = new CACSLLocation(node);
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        ArrayList<Statement> stmt = new ArrayList<Statement>();

        ResultExpression condResult = (ResultExpression) main.dispatch(
        				node.getConditionExpression());
        condResult = condResult.switchToRValue(main, memoryHandler, structHandler, loc);
        Expression cond = condResult.lrVal.getValue();
        decl.addAll(condResult.decl);
        stmt.addAll(condResult.stmt);
        List<HavocStatement> havocs = Dispatcher
                .createHavocsForAuxVars(condResult.auxVars);

        Result thenResult = main.dispatch(node.getThenClause());
        List<Statement> thenStmt = new ArrayList<Statement>();
        thenStmt.addAll(havocs);
        if (thenResult instanceof ResultExpression) {
            ResultExpression re = (ResultExpression) thenResult;
            decl.addAll(re.decl);
            thenStmt.addAll(re.stmt);
        } else if (thenResult instanceof Result) {
            if (thenResult.node instanceof Body) {
                Body thenPart = (Body) (thenResult.node);
                thenStmt.addAll(Arrays.asList(thenPart.getBlock()));
                decl.addAll(Arrays.asList(thenPart.getLocalVars()));
            } else {
                String msg = "Error: unexpected dispatch result";
                Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
                throw new IncorrectSyntaxException(msg);
            }
        }

        List<Statement> elseStmt = new ArrayList<Statement>();
        elseStmt.addAll(havocs);
        if (node.getElseClause() != null) {
            Result elseResult = main.dispatch(node.getElseClause());
            if (elseResult instanceof ResultExpression) {
                ResultExpression re = (ResultExpression) elseResult;
                decl.addAll(re.decl);
                elseStmt.addAll(re.stmt);
            } else if (elseResult instanceof Result) {
                if (elseResult.node instanceof Body) {
                    Body elsePart = (Body) (elseResult.node);
                    elseStmt.addAll(Arrays.asList(elsePart.getBlock()));
                    decl.addAll(Arrays.asList(elsePart.getLocalVars()));
                }
            } else {
                String msg = "Error: unexpected dispatch result";
                Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
                throw new IncorrectSyntaxException(msg);
            }
        }
        assert thenStmt != null;
        assert elseStmt != null;
        cond = main.typeHandler.convertArith2Boolean(loc, new PrimitiveType(
                loc, SFO.BOOL), cond);
        // TODO : handle if(pointer), if(pointer==NULL) and if(pointer==0)
        stmt.add(new IfStatement(loc, cond, thenStmt.toArray(new Statement[0]),
                elseStmt.toArray(new Statement[0])));
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        return new ResultExpression(stmt, null, decl, emptyAuxVars);
    }

    /**
     * Method that handles loops (for, while, do/while). Each of corresponding
     * visit methods will call this method.
     * 
     * @param main
     *            the main dispatcher
     * @param node
     *            the node to visit
     * @param bodyResult
     *            the body component of the corresponding loop
     * @param condResult
     *            the condition of the loop
     * @return a result object holding the translated loop (i.e. a while loop)
     */
    private Result handleLoops(Dispatcher main, IASTStatement node,
            Result bodyResult, ResultExpression condResult) {
    	int scopeDepth = symbolTable.getActiveScopeNum();
        assert node instanceof IASTWhileStatement
                || node instanceof IASTDoStatement
                || node instanceof IASTForStatement;

        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        CACSLLocation loc = new CACSLLocation(node);

        Result iterator = null;
        if (node instanceof IASTForStatement) {
            IASTForStatement forStmt = (IASTForStatement) node;
            // add initialization for this for loop
            IASTStatement cInitStmt = forStmt.getInitializerStatement();
            if (cInitStmt != null) {
                symbolTable.beginScope();
                Result initializer = main.dispatch(cInitStmt);
                if (initializer instanceof ResultExpression) {
                    ResultExpression rExp = (ResultExpression) initializer;
                    stmt.addAll(rExp.stmt);
                    decl.addAll(rExp.decl);
                } else if (initializer instanceof ResultSkip) {
                    // this is an empty statement in the C Code. We will skip it
                } else {
                    String msg = "Uninplemented type of for loop initialization: "
                            + initializer.getClass();
                    Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax,
                            msg);
                    throw new UnsupportedSyntaxException(msg);
                }
            }

            // translate iterator
            IASTExpression cItExpr = forStmt.getIterationExpression();
            if (cItExpr != null)
                iterator = main.dispatch(cItExpr);

            // translate condition
            IASTExpression cCondExpr = forStmt.getConditionExpression();
            if (cCondExpr != null)
                condResult = (ResultExpression) main.dispatch(cCondExpr);
            else
                condResult = new ResultExpression(new RValue(new BooleanLiteral(loc,
                        new InferredType(Type.Boolean), true)),
                        new HashMap<VariableDeclaration, CACSLLocation>(0));

            bodyResult = main.dispatch(forStmt.getBody());
        }
        assert (main.isAuxVarMapcomplete(condResult.decl, condResult.auxVars));

        ArrayList<Statement> bodyBlock = new ArrayList<Statement>();
        if (bodyResult instanceof ResultExpression) {
            ResultExpression re = (ResultExpression) bodyResult;
            decl.addAll(re.decl);
            bodyBlock.addAll(re.stmt);
        } else if (bodyResult instanceof Result) {
            if (bodyResult.node instanceof Body) {
                Body body = (Body) (bodyResult.node);
                bodyBlock.addAll(Arrays.asList(body.getBlock()));
                decl.addAll(Arrays.asList(body.getLocalVars()));
            } else {
                String msg = "Error: unexpected dispatch result"
                        + bodyResult.getClass();
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
        }

        if (node instanceof IASTForStatement && iterator != null) {
            // add iterator statements of this for loop
            if (iterator instanceof ResultExpressionList) {
                for (ResultExpression el : ((ResultExpressionList) iterator).list) {
                    bodyBlock.addAll(el.stmt);
                    decl.addAll(el.decl);
                    assert (main.isAuxVarMapcomplete(el.decl, el.auxVars));
                    bodyBlock.addAll(Dispatcher
                            .createHavocsForAuxVars(el.auxVars));
                }
            } else if (iterator instanceof ResultExpression) {
                ResultExpression iteratorRE = (ResultExpression) iterator;
                bodyBlock.addAll(iteratorRE.stmt);
                decl.addAll(iteratorRE.decl);
                assert (main.isAuxVarMapcomplete(iteratorRE.decl,
                        iteratorRE.auxVars));
                bodyBlock.addAll(Dispatcher
                        .createHavocsForAuxVars(iteratorRE.auxVars));
            } else {
                String msg = "Uninplemented type of loop iterator: "
                        + iterator.getClass();
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
        }

        condResult = condResult.switchToRValue(main, memoryHandler, structHandler, loc);
        decl.addAll(condResult.decl);
        Expression condExpr = main.typeHandler.convertArith2Boolean(loc,
                new PrimitiveType(loc, SFO.BOOL), condResult.lrVal.getValue());
        IfStatement ifStmt;
        {
            Expression cond = new UnaryExpression(loc,
                    UnaryExpression.Operator.LOGICNEG, condExpr);
            ArrayList<Statement> thenStmt = new ArrayList<Statement>(
                    Dispatcher.createHavocsForAuxVars(condResult.auxVars));
            thenStmt.add(new BreakStatement(loc));
            Statement[] elseStmt = Dispatcher.createHavocsForAuxVars(
                    condResult.auxVars).toArray(new Statement[0]);
            ifStmt = new IfStatement(loc, cond,
                    thenStmt.toArray(new Statement[0]), elseStmt);
        }

        if (node instanceof IASTWhileStatement
                || node instanceof IASTForStatement) {
            bodyBlock.add(0, ifStmt);
            bodyBlock.addAll(0, condResult.stmt);
        } else if (node instanceof IASTDoStatement) {
            bodyBlock.addAll(condResult.stmt);
            bodyBlock.add(ifStmt);
        }

        LoopInvariantSpecification[] spec;
        if (contract == null) {
            spec = new LoopInvariantSpecification[0];
        } else {
			List<LoopInvariantSpecification> specList = 
					new ArrayList<LoopInvariantSpecification>();
			if (node instanceof IASTForStatement) {
				for (int i = 0; i < contract.size(); i++) {
					// retranslate ACSL specification needed e.g., in cases
					// where ids of function parameters differ from is in ACSL
					// expression
					Result retranslateRes = main.dispatch(contract.get(i));
					if (retranslateRes instanceof ResultContract) {
						ResultContract resContr = (ResultContract) retranslateRes;
						assert resContr.specs.length == 1;
						for (Specification cSpec : resContr.specs) {
							specList.add((LoopInvariantSpecification) cSpec);
						}
					} else {
						specList.add((LoopInvariantSpecification) retranslateRes.node);
					}
				}
				if (((IASTForStatement) node).getInitializerStatement() != null) {
					main.cHandler.getSymbolTable().endScope();
				}
			}
			spec = specList.toArray(new LoopInvariantSpecification[0]);
            clearContract(); // take care for behavior and completeness
        }

        stmt.add(new WhileStatement(loc, new BooleanLiteral(loc,
                new InferredType(Type.Boolean), true), spec, bodyBlock
                .toArray(new Statement[0])));
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        assert (symbolTable.getActiveScopeNum() == scopeDepth);
        return new ResultExpression(stmt, null, decl, emptyAuxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTWhileStatement node) {
        ResultExpression condResult =
        		(ResultExpression) main.dispatch(node.getCondition());
        Result bodyResult = main.dispatch(node.getBody());
        return handleLoops(main, node, bodyResult, condResult);
    }

    @Override
    public Result visit(Dispatcher main, IASTForStatement node) {
        return handleLoops(main, node, null, null);
    }

    @Override
    public Result visit(Dispatcher main, IASTDoStatement node) {
        ResultExpression condResult =
        		(ResultExpression) main.dispatch(node.getCondition());
        Result bodyResult = main.dispatch(node.getBody());
        return handleLoops(main, node, bodyResult, condResult);
    }

    @Override
    public Result visit(Dispatcher main, IASTExpressionList node) {
        ResultExpressionList result = new ResultExpressionList();
        for (IASTExpression expr : node.getExpressions()) {
            Result r = main.dispatch(expr);
            assert r instanceof ResultExpression;
            result.list.add((ResultExpression) r);
        }
        return result;
    }

    @Override
    public Result visit(Dispatcher main, IASTInitializerList node) {
        CACSLLocation loc = new CACSLLocation(node);
        if (node.getClauses().length != node.getSize()) {
            throw new IllegalArgumentException(
                    "You might have parsed your code with " +
                    "ITranslationUnit.AST_SKIP_TRIVIAL_EXPRESSIONS_IN_AGGREGATE_INITIALIZERS!");
        }
        ResultExpressionListRec result = new ResultExpressionListRec();
        for (IASTInitializerClause i : node.getClauses()) {
            Result r = main.dispatch(i);
            if (r instanceof ResultExpressionListRec) {
                result.list.add((ResultExpressionListRec) r);
            } else if (r instanceof ResultExpression) {
                ResultExpression rex = (ResultExpression) r;
                rex = rex.switchToRValue(main, memoryHandler, structHandler, loc);
                result.list.add(new ResultExpressionListRec(rex.stmt, rex.lrVal,
                        rex.decl, rex.auxVars));
                result.auxVars.putAll(((ResultExpression) r).auxVars);
            } else {
                String msg = "Unexpected result";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
        }
        return result;
    }

    @Override
    public Result visit(Dispatcher main, CASTDesignatedInitializer node) {
//        return structHandler.handleDesignatedInitializer(main, node);
        return structHandler.handleDesignatedInitializer(main, memoryHandler, structHandler, node);
    }

    @Override
    public Result visit(Dispatcher main, IASTFunctionCallExpression node) {
        return functionHandler.handleFunctionCallExpression(main,
                memoryHandler, structHandler, node);
    }

    @Override
    public Result visit(Dispatcher main, IASTBreakStatement node) {
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        stmt.add(new BreakStatement(new CACSLLocation(node)));
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>();
        return new ResultExpression(stmt, null, new ArrayList<Declaration>(),
                emptyAuxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTNullStatement node) {
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTSwitchStatement node) {
        // FIXME : This is not exactly as described in C99 standard!
        // declarations are allowed like this:
        // switch ([COND])
        // { [DECL]* [[CASE|DEFAULT]+ [STMT]+ [DECL|STMT]* [BREAK]?] }
        // we allow DECLS after case|default atm but no decls at the beginning!
        CACSLLocation loc = new CACSLLocation(node);
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
        Result switchParam = main.dispatch(node.getControllerExpression());
        assert switchParam instanceof ResultExpression;
        ResultExpression l = ((ResultExpression) switchParam).switchToRValue(main, memoryHandler, structHandler, loc);
        stmt.addAll(l.stmt);
        decl.addAll(l.decl);
        auxVars.putAll(l.auxVars);
        Expression switchArg = l.lrVal.getValue();
        Expression cond = null;
        boolean isFirst = true;
        String breakLabelName = "SWITCH~BREAK~" + node.hashCode();

        ArrayList<Statement> ifBlock = new ArrayList<Statement>();
        symbolTable.beginScope();
        for (IASTNode child : node.getBody().getChildren()) {
            CACSLLocation locC = new CACSLLocation(child);
            if (isFirst
                    && !(child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement)) {
                String msg = "A case/default statement is expected at the beginning of a switch block!";
                Dispatcher.error(locC, SyntaxErrorType.IncorrectSyntax, msg);
                throw new IncorrectSyntaxException(msg);
            }
            checkForACSL(main, ifBlock, child, null);
            Result r = main.dispatch(child);
            if (r instanceof ResultExpression) {
                ResultExpression res = (ResultExpression) r;
                if (child instanceof IASTCaseStatement
                        || child instanceof IASTDefaultStatement) {
                    if (!isFirst && ifBlock.size() > 0) {
                        IfStatement ifStmt = new IfStatement(locC, cond,
                                ifBlock.toArray(new Statement[0]),
                                new Statement[0]);
                        stmt.add(ifStmt);
                    }
                    isFirst = false;
                    Expression thisCase;
                    if (child instanceof IASTCaseStatement)
                        thisCase = new BinaryExpression(locC, Operator.COMPEQ,
                                switchArg, res.lrVal.getValue());
                    else /* default statement */
                        thisCase = res.lrVal.getValue();
                    
                    if (cond == null) {
                    	cond = thisCase;
                    } else {
                        cond = new BinaryExpression(locC, Operator.LOGICOR,
                                cond, thisCase);
                    }
                    ifBlock = new ArrayList<Statement>();
                }
                decl.addAll(res.decl);
                auxVars.putAll(res.auxVars);
                for (Statement s : res.stmt)
                    if (s instanceof BreakStatement)
                        ifBlock.add(new GotoStatement(locC,
                                new String[] { breakLabelName }));
                    else
                        ifBlock.add(s);
            }
            if (r.node != null && r.node instanceof Body) {
                // we already have a unique naming for variables! -> unfold
                Body b = ((Body) r.node);
                decl.addAll(Arrays.asList(b.getLocalVars()));
                stmt.addAll(Arrays.asList(b.getBlock()));
            }
        }
        assert cond != null;
        if (ifBlock.size() > 0) {
            IfStatement ifStmt = new IfStatement(loc, cond,
                    ifBlock.toArray(new Statement[0]), new Statement[0]);
            stmt.add(ifStmt);
        }
        checkForACSL(main, stmt, null, node);
        stmt.add(new Label(loc, breakLabelName));
        stmt.addAll(Dispatcher.createHavocsForAuxVars(auxVars));
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        return new ResultExpression(stmt, null, decl, emptyAuxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTCaseStatement node) {
        ResultExpression c = (ResultExpression) main.dispatch(node
                .getExpression());
        return c.switchToRValue(main, memoryHandler, structHandler, new CACSLLocation(node));
    }

    @Override
    public Result visit(Dispatcher main, IASTDefaultStatement node) {
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        return new ResultExpression(stmt, 
        		new RValue(new BooleanLiteral(new CACSLLocation(node), new InferredType(Type.Boolean), true)), 
        		decl, emptyAuxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTLabelStatement node) {
        CACSLLocation loc = new CACSLLocation(node);
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        String label = node.getName().toString();
        if (m_ErrorLabelWarning && label.equals("ERROR")) {
        	String shortDescription = "ERROR label found";
        	String longDescription =  "The label \"ERROR\" does not have a special meaning in the translation mode you selected. You might want to change your settings and use the SV-COMP translation mode.";  
        	Dispatcher.warn(loc, shortDescription, longDescription);
        }
        stmt.add(new Label(loc, label));
        Result r = main.dispatch(node.getNestedStatement());
        if (r instanceof ResultExpression) {
            ResultExpression res = (ResultExpression) r;
            decl.addAll(res.decl);
            stmt.addAll(res.stmt);
            return new ResultExpression(stmt, res.lrVal, decl, emptyAuxVars);
        } else if (r instanceof ResultSkip) {
            return new ResultExpression(stmt, null, decl, emptyAuxVars);
        } else { // r instanceof Result ...
            RValue expr = null;
            if (r.node instanceof Statement) {
                stmt.add((Statement) r.node);
            } else if (r.node instanceof Declaration) {
                decl.add((Declaration) r.node);
            } else if (r.node instanceof Expression) {
                expr = new RValue((Expression) r.node);
            } else if (r.node instanceof Body) {
                // we already have a unique naming for variables! --> unfold
                Body b = ((Body) r.node);
                decl.addAll(Arrays.asList(b.getLocalVars()));
                stmt.addAll(Arrays.asList(b.getBlock()));
            } else {
                String msg = "Unexpected boogie AST node type: "
                        + r.node.getClass();
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
            return new ResultExpression(stmt, expr, decl, emptyAuxVars);
        }
    }
    
    public Result handleLabelCommonCode(Dispatcher main, IASTLabelStatement node, CACSLLocation loc) {

        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        String label = node.getName().toString();
        stmt.add(new Label(loc, label));
        Result r = main.dispatch(node.getNestedStatement());
        if (r instanceof ResultExpression) {
            ResultExpression res = (ResultExpression) r;
            decl.addAll(res.decl);
            stmt.addAll(res.stmt);
            return new ResultExpression(stmt, res.lrVal, decl, emptyAuxVars);
        } else if (r instanceof ResultSkip) {
            return new ResultExpression(stmt, null, decl, emptyAuxVars);
        } else { // r instanceof Result ...
            RValue expr = null;
            if (r.node instanceof Statement) {
                stmt.add((Statement) r.node);
            } else if (r.node instanceof Declaration) {
                decl.add((Declaration) r.node);
            } else if (r.node instanceof Expression) {
                expr = new RValue((Expression) r.node);
            } else if (r.node instanceof Body) {
                // we already have a unique naming for variables! --> unfold
                Body b = ((Body) r.node);
                decl.addAll(Arrays.asList(b.getLocalVars()));
                stmt.addAll(Arrays.asList(b.getBlock()));
            } else {
                String msg = "Unexpected boogie AST node type: "
                        + r.node.getClass();
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
            return new ResultExpression(stmt, expr, decl, emptyAuxVars);
        }
    }
    

    @Override
    public Result visit(Dispatcher main, IASTGotoStatement node) {
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        String[] name = new String[] { node.getName().toString() };
        stmt.add(new GotoStatement(new CACSLLocation(node), name));
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        return new ResultExpression(stmt, null, new ArrayList<Declaration>(),
                emptyAuxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTCastExpression node) {
        Result expr = main.dispatch(node.getOperand());
        // TODO : review decision to only drop casts!
        // This can of course lead to type errors (e.g. int i = 1.0f;)
        String msg = "Ignored cast! At line: "
                + node.getFileLocation().getStartingLineNumber();
        Dispatcher.unsoundnessWarning(new CACSLLocation(node), msg,
                "Ignored cast!");
        return expr;
    }
    
    @Override
    public Result visit(Dispatcher main, IASTConditionalExpression node) {
        CACSLLocation loc = new CACSLLocation(node);
        assert node.getChildren().length == 3;
        Result resLocCond = main.dispatch(node.getLogicalConditionExpression());
        assert resLocCond instanceof ResultExpression;
        ResultExpression reLocCond = (ResultExpression) resLocCond;
        reLocCond = reLocCond.switchToRValue(main, memoryHandler, structHandler, loc);
        
        Result rPositive = main.dispatch(node.getPositiveResultExpression());
        assert rPositive instanceof ResultExpression;
        ResultExpression rePositive = (ResultExpression) rPositive;
        rePositive = reLocCond.switchToRValue(main, memoryHandler, structHandler, loc);
        
        Result rNegative = main.dispatch(node.getNegativeResultExpression());
        assert rNegative instanceof ResultExpression;
        ResultExpression reNegative = (ResultExpression) rNegative;
        reNegative = reLocCond.switchToRValue(main, memoryHandler, structHandler, loc);
        
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        Map<VariableDeclaration, CACSLLocation> auxVars = 
        		new HashMap<VariableDeclaration, CACSLLocation>(0);
        decl.addAll(reLocCond.decl);
        stmt.addAll(reLocCond.stmt);
        String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.ITE);
        InferredType tmpIType = (InferredType) rePositive.lrVal.getValue().getType();
        assert (tmpIType.equals(reNegative.lrVal.getValue().getType()));
        VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
        decl.add(tmpVar);
        Expression condition = reLocCond.lrVal.getValue();
        condition = main.typeHandler.convertArith2Boolean(loc, new PrimitiveType(
                loc, SFO.BOOL), condition);
        List<Statement> ifStatements = new ArrayList<Statement>();
        {
        	ifStatements.addAll(rePositive.stmt);
        	LeftHandSide[] lhs = { new VariableLHS(loc, tmpName) };
        	AssignmentStatement assign = new AssignmentStatement(loc, lhs, 
        			new Expression[] { rePositive.lrVal.getValue() });
        	ifStatements.add(assign);
        	List<HavocStatement> havocAuxVars = Dispatcher
                    .createHavocsForAuxVars(rePositive.auxVars);
        	ifStatements.addAll(havocAuxVars);
        	decl.addAll(rePositive.decl);
        }
        
        List<Statement> elseStatements = new ArrayList<Statement>();
        {
        	elseStatements.addAll(reNegative.stmt);
        	LeftHandSide[] lhs = { new VariableLHS(loc, tmpName) };
        	AssignmentStatement assign = new AssignmentStatement(loc, lhs, 
        					new Expression[] { reNegative.lrVal.getValue() });
        	elseStatements.add(assign);
        	List<HavocStatement> havocAuxVars = Dispatcher
                    .createHavocsForAuxVars(reNegative.auxVars);
        	elseStatements.addAll(havocAuxVars);
        	decl.addAll(reNegative.decl);
        }
        Statement ifStatement = new IfStatement(loc, condition, 
        		ifStatements.toArray(new Statement[0]), 
        		elseStatements.toArray(new Statement[0]));
        stmt.add(ifStatement);
       
        IdentifierExpression tmpExpr = new IdentifierExpression(loc, tmpName);
    	List<HavocStatement> havocAuxVars = Dispatcher
                .createHavocsForAuxVars(reLocCond.auxVars);
    	stmt.addAll(havocAuxVars);
        auxVars.put(tmpVar,loc);
        return new ResultExpression(stmt, new RValue(tmpExpr), decl, auxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTArraySubscriptExpression node) {
        return arrayHandler
        		.handleArraySubscriptionExpression(main, memoryHandler, structHandler, node);
    }

    @Override
    public Result visit(Dispatcher main, IASTInitializerClause node) {
        assert node.getChildren().length == 1;
        Result r = main.dispatch(node.getChildren()[0]);
        assert r instanceof ResultExpression;
        ResultExpression rex = (ResultExpression) r;
        return rex.switchToRValue(main, memoryHandler, structHandler, new CACSLLocation(node));
    }

    @Override
    public Result visit(Dispatcher main, IASTFieldReference node) {
        return structHandler.handleFieldReference(main, node, memoryHandler);
    }

    @Override
    public Result visit(Dispatcher main, IASTPointer node) {
        // TODO : implement pointer IASTPointer? When is this required?!
        throw new UnsupportedOperationException(
                "This should have been handled before ...");
    }

    @Override
    public Result visit(Dispatcher main, IASTProblemStatement node) {
        String msg = "Syntax error (statement problem) in C program: "
                + node.getProblem().getMessage();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.IncorrectSyntax, msg);
        throw new IncorrectSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTProblemDeclaration node) {
        String msg = "Syntax error (declaration problem) in C program: "
                + node.getProblem().getMessage();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.IncorrectSyntax, msg);
        throw new IncorrectSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTProblemExpression node) {
        String msg = "Syntax error (expression problem) in C program: "
                + node.getProblem().getMessage();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.IncorrectSyntax, msg);
        throw new IncorrectSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTProblem node) {
        String msg = "Syntax error in C program: " + node.getMessage();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.IncorrectSyntax, msg);
        throw new IncorrectSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTProblemTypeId node) {
        String msg = "Syntax error (type ID problem) in C program: "
                + node.getProblem().getMessage();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.IncorrectSyntax, msg);
        throw new IncorrectSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTTypeIdExpression node) {
        ILocation loc = new CACSLLocation(node);
        switch (node.getOperator()) {
            case IASTTypeIdExpression.op_sizeof:
                Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                        0);
                return new ResultExpression(new RValue(memoryHandler.getSizeOf(main, node
                        .getTypeId().getDeclSpecifier())), emptyAuxVars);
            default:
                break;
        }
        String msg = "Unsupported boogie AST node type: " + node.getClass();
        Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    /**
     * Wraps a binary Boolean expression into a Boogie if-then-else expression
     * of type integer.
     * 
     * {@link wrapBinaryBoolean2Int(loc, expr)}
     * @param loc location
     * @param op binary operator
     * @param lexpr left expression
     * @param rexpr right expression
     * @return wrapped expression
     * @author Christian
     */
    private Expression wrapBinaryBoolean2Int(final CACSLLocation loc,
    		final Operator op, final Expression lexpr, final Expression rexpr) {
		return wrapBoolean2Int(loc, new BinaryExpression(loc,
				new InferredType(Type.Boolean), op, lexpr, rexpr));
	}
    
    /**
     * Wraps a Boolean expression into a Boogie if-then-else expression of type
     * integer. Example:
     * Input: <code>x == 0</code>
     * Output: <code>(x == 0) ? 1 : 0</code>
     * 
     * @param loc location
     * @param expr Boolean expression
     * @return wrapped expression
     * @author Christian
     */
    private Expression wrapBoolean2Int(final CACSLLocation loc,
    		final Expression expr) {
		return new IfThenElseExpression(loc, new InferredType(Type.Integer),
    			expr,
    			new IntegerLiteral(loc, SFO.NR1),
    			new IntegerLiteral(loc, SFO.NR0));
	}
    
    void addHeapModifiedGlobals() {
    	for (String t : new String[] { SFO.INT, SFO.POINTER,
    			SFO.REAL, SFO.BOOL }) {
    		functionHandler.getModifiedGlobals()
    		.get(functionHandler.getCurrentProcedureID())
    		.add(SFO.MEMORY + "_" + t);
    	}
    }

    @Override
    public SymbolTable getSymbolTable() {
        return symbolTable;
    }

    @Override
    public void clearContract() {
        this.contract.clear();
    }

    @Override
    public void addSizeOfConstants(CType cvar) {
        memoryHandler.calculateSizeOf(cvar);
    }
}
