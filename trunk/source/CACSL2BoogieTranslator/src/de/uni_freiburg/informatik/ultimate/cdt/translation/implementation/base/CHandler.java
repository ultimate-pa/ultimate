/**
 * The base C handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.text.ParseException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
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
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
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
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;

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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue.StorageClass;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultContract;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionList;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionListRec;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ConvExpr;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Backtranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.Check;

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
	public MemoryHandler memoryHandler;
	/**
	 * Post processor.
	 */
	protected PostProcessor postProcessor;
	
	protected ITypeHandler typeHandler;
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
	protected HashMap<String, FunctionDeclaration> mFunctions;
	/**
	 * A set holding declarations of global variables required for variables,
	 * declared locally in C but required to be global in Boogie. e.g. constants
	 * for enums or local static variables. Each declaration can have a set of
	 * initialization statements.
	 * So the procedure is:
	 *  typeDeclarations: added to this map in IASTSimpleDeclaration, 
	 *    declared using this map in ITranslationUnit
	 *  static variables: added to this map in IASTSimpleDeclaration,
	 *    declared using this map in ITranslationUnit,
	 *    initialized using this map in PostProcessor.createInit..()
	 *  global variables: added to this map in IASTTranslationUnit,
	 *    declared using this map in ITranslationUnit,
	 *    initialized using this map in PostProcessor.createInit..()
	 */
	protected HashMap<Declaration, CDeclaration> mDeclarationsGlobalInBoogie;
	
	/**
	 * A collection of axioms generated during translation process.
	 */
	protected HashSet<Axiom> mAxioms;

	/**
	 * Translation from Boogie to C for traces and expressions.
	 */
	protected final Backtranslator backtranslator;

	/**
	 * If set to true and the program contains an error label ULTIMATE shows
	 * a warning that suggests a different translation mode.
	 */
	protected final boolean mErrorLabelWarning;
	private HashSet<String> mBoogieIdsOfHeapVars;

	/**
	 * This is a stack containing the types of the things declared
	 * IASTDeclarator nodes.  The last element on the stack corresponds to
	 * the type of the current (inner) declarator node.  There may be several
	 * types on this stack if the declarators are nested, as in
	 * <pre>int *(*a(int))[3]</pre>
	 * which declares a function returning a pointer to an array of length
	 * three containing int pointers. There are three nested declarators:
	 * A PointerDeclarator contains an ArrayDeclarator contains a Pointer
	 * contains a function.  
	 */
	private ArrayDeque<ResultTypes> mCurrentDeclaredTypes;
	
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
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		boolean checkPointerValidity = prefs.getBoolean(PreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY);
		this.memoryHandler = new MemoryHandler(checkPointerValidity);
		this.symbolTable = new SymbolTable(main);
		this.mFunctions = new HashMap<String, FunctionDeclaration>();
		this.mDeclarationsGlobalInBoogie = new HashMap<Declaration, CDeclaration>();
		this.mAxioms = new HashSet<Axiom>();
		this.backtranslator = backtranslator;
		this.contract = new ArrayList<ACSLNode>();
		this.mErrorLabelWarning = errorLabelWarning;

		this.mBoogieIdsOfHeapVars = new HashSet<String>();
		this.mCurrentDeclaredTypes = new ArrayDeque<ResultTypes>();
	}

	@Override
	public Result visit(Dispatcher main, IASTNode node) {
		String msg = "CHandler: Not yet implemented: \""
				+ node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		ILocation loc = new CACSLLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
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
									ILocation loc = new CACSLLocation(parent);
							        Dispatcher.unsupportedSyntax(loc, msg);
								}
							}
						} else {
							String msg = "Unexpected ACSL comment: "
									+ acslResult.node.getClass();
							ILocation loc = new CACSLLocation(parent);
							throw new IncorrectSyntaxException(loc, msg);
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
							ILocation loc = new CACSLLocation(next);
							throw new IncorrectSyntaxException(loc, msg);
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
					ILocation loc = new CACSLLocation(parent);
			        Dispatcher.unsupportedSyntax(loc, msg);
				}
			}
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTTranslationUnit node) {
		this.typeHandler = main.typeHandler;//FIXME -- not such a nice solution (but typeHandler is null at CHandler constructor)
		
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
			Dispatcher.unsupportedSyntax(loc, msg);
		}
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		
		for (IASTNode child : node.getChildren()) {
			checkForACSL(main, null, child, null);
			Result childRes = main.dispatch(child);
			
			if (childRes instanceof ResultDeclaration) {
				// we have to add a global variable
				ResultDeclaration rd = (ResultDeclaration) childRes;
				for (CDeclaration cd : rd.getDeclarations()) {
					mDeclarationsGlobalInBoogie.put(symbolTable.getBoogieDeclOfResultDecl(cd), cd);
				}
			} else {
				if (childRes instanceof ResultSkip)
					continue;
				assert childRes.getClass() == Result.class;
				assert childRes.node != null;
				decl.add((Declaration) childRes.node);
			}
		}
		
		// Christian: function pointers
        String[] constants = new String[
                ((MainDispatcher) main).getFunctionPointers().size()];
		if (constants.length > 0) {
	        int i = 0;
	        for (final String cId : ((MainDispatcher) main).
	                getFunctionPointers().keySet()) {
	            constants[i++] = SFO.FUNCTION_ADDRESS + cId;
	        }
    		VarList varList = new VarList(loc, constants,
                    MemoryHandler.POINTER_TYPE);
    		decl.add(new ConstDeclaration(loc, new Attribute[0], true,
                    varList, null, false));
		}
		
		for (Declaration d : mDeclarationsGlobalInBoogie.keySet()) {
			assert d instanceof ConstDeclaration
			|| d instanceof VariableDeclaration
			|| d instanceof TypeDeclaration;
			decl.add(d);
		}
		decl.addAll(mAxioms);
		if (!functionHandler.isEveryCalledProcedureDeclared()) {
			String msg = "A method was called but never declared!";
			throw new IncorrectSyntaxException(loc, msg);
		}

		decl.addAll(postProcessor.postProcess(main, loc, memoryHandler, arrayHandler, functionHandler, structHandler,
				functionHandler.getProcedures(),
				functionHandler.getModifiedGlobals(),
				main.typeHandler.getUndefinedTypes(), this.mFunctions.values(),
				mDeclarationsGlobalInBoogie
				));
		
		//this has to happen after postprocessing as pping may add sizeof constants for initializations
		decl.addAll(memoryHandler.declareMemoryModelInfrastructure(main, loc));
		
		// handle proc. declaration & resolve their transitive modified globals
		decl.addAll(functionHandler.calculateTransitiveModifiesClause(main));
		return new Result(new Unit(loc, decl.toArray(new Declaration[0])));
	}

	@Override
	public Result visit(Dispatcher main, IASTFunctionDefinition node) {
		ResultTypes resType = (ResultTypes) main.dispatch(node.getDeclSpecifier());
		
		mCurrentDeclaredTypes.push(resType);
		ResultDeclaration declResult = (ResultDeclaration) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return functionHandler.handleFunctionDefinition(main, memoryHandler, node, declResult);
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

		if (isNewScopeRequired(parent))
			this.beginScope();
//			symbolTable.beginScope();

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
		if (isNewScopeRequired(parent)){
			stmt = functionHandler.insertMallocs(main, loc, memoryHandler, stmt);
			for (SymbolTableValue stv : symbolTable.currentScopeValues()) {
				if (!stv.isGlobalVar()) {
					decl.add(stv.getBoogieDecl());
				}
			}
			
			this.endScope();
		}
		return new Result(new Body(loc,
				decl.toArray(new VariableDeclaration[0]),
				stmt.toArray(new Statement[0])));
	}

	/**
	 * Visit the SimpleDeclaration (which may be quite complex in fact..).
	 * The return value here may have different uses:
	 *  - for global variables and declarations inside of struct definitions, it is a
	 *    ResultDeclaration (containing the Boogie Declaration of the variable)
	 *  - for local variables that have an initializer, a ResultExpression is returned
	 *    which contains (Boogie) statements and declarations that make the initialization
	 *    according to the initializer
	 * The declarations themselves of the local variables (and f.i. typedefs) are stored in the 
	 * symbolTable and inserted into the Boogie code at the next endScope() 
	 * Declarations of static variables are added to mDeclarationsGlobalInBoogie such that they
	 * can be declared and initialized globally.
	 * Variables/types that are global in Boogie but not in C are stored in the 
	 * Symboltable to keep the association of BoogieId and CId.
	 */
	@Override
	public Result visit(Dispatcher main, IASTSimpleDeclaration node) {
		CACSLLocation loc = new CACSLLocation(node);
		if (node.getDeclSpecifier() == null) {
			String msg = "This statement can be removed!";
			Dispatcher.warn(loc, msg);
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
			Result result = new ResultSkip(); //Skip will be overwritten in case of a global or a local initialized variable
			
			StorageClass storageClass = scConstant2StorageClass(node.getDeclSpecifier().getStorageClass());
			
			mCurrentDeclaredTypes.push(resType);
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
				ResultDeclaration declResult = (ResultDeclaration) main.dispatch(d);
				
				//update symbol table
				for (CDeclaration cDec : declResult.getDeclarations()) {
					
					if (cDec.getType() instanceof CFunction) {
						functionHandler.handleFunctionDeclarator(main, contract, 
								(IASTFunctionDeclarator) d, (CFunction) cDec.getType(), resType);
						continue;
					}	
					
					boolean onHeap = cDec.isOnHeap();
					String bId = main.nameHandler.getUniqueIdentifier(node, cDec.getName(), 
							symbolTable.getCompoundCounter(), onHeap);
					if (onHeap) 
						mBoogieIdsOfHeapVars.add(bId);
					
					Declaration boogieDec = null;
					boolean globalInBoogie = false;
					ASTType translatedType = null;
					if (onHeap)
						translatedType = MemoryHandler.POINTER_TYPE;
					else
						translatedType = main.typeHandler.ctype2asttype(loc, cDec.getType());
					
					if (storageClass == StorageClass.TYPEDEF) {
						boogieDec = new TypeDeclaration(loc, new Attribute[0], false, 
								bId, new String[0] , translatedType);
//						main.typeHandler.addDefinedType(bId, mCurrentDeclaredTypes.peek());
						main.typeHandler.addDefinedType(bId, 
								new ResultTypes(new NamedType(loc, cDec.getName(), null), false, false, cDec.getType()));
						//TODO: add a sizeof-constant for the type??
						globalInBoogie = true;
						mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
					/* global static variables are treated like normal global variables.. */
					} else if (storageClass == StorageClass.STATIC && !functionHandler.noCurrentProcedure()) {
						boogieDec = new VariableDeclaration(loc, new Attribute[0],
								new VarList[] { new VarList(loc, new String[] {bId}, 
										translatedType) });
						globalInBoogie = true;
						mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
					} else {
						if (cDec.getInitializer() == null && !functionHandler.noCurrentProcedure()) { 
							//in case of a local variable declaration without an initializer, we don't modify
							// the result
							assert result instanceof ResultSkip || result instanceof ResultExpression;
						} else if (cDec.getInitializer() != null && !functionHandler.noCurrentProcedure()) { 
							//in case of a local variable declaration with an initializer, the statements and delcs
							// necessary for the initialization are the result
							assert result instanceof ResultSkip || result instanceof ResultExpression;
							ResultExpression initRex = 
									PostProcessor.initVar(loc, main, memoryHandler, arrayHandler, functionHandler, structHandler, 
											new VariableLHS(loc, bId), cDec.getType(), cDec.getInitializer());
							if (result instanceof ResultSkip)
								result = new ResultExpression((LRValue) null);

							((ResultExpression) result).stmt.addAll(initRex.stmt);
							((ResultExpression) result).decl.addAll(initRex.decl);
							((ResultExpression) result).auxVars.putAll(initRex.auxVars);
							((ResultExpression) result).overappr.addAll(initRex.overappr);
						} else {
							//in case of global variables, the result is the declaration, initialization is
							//done in the postProcessor
							//in case this simpleDeclaration is part of a struct definition, we also need the 
							//Declarations as a result
							assert result instanceof ResultSkip || result instanceof ResultDeclaration;
							if (result instanceof ResultSkip)
								result = new ResultDeclaration();
							((ResultDeclaration) result).addDeclaration(cDec);
						}
						boogieDec = new VariableDeclaration(loc, new Attribute[0],
								new VarList[] { new VarList(loc, new String[] {bId}, 
										translatedType) });
						globalInBoogie = functionHandler.noCurrentProcedure();
					}
					
					symbolTable.put(cDec.getName(), new SymbolTableValue(bId,
							boogieDec, cDec, globalInBoogie,
							storageClass)); 
				}
			}
			mCurrentDeclaredTypes.pop();
			return result;
		}
		String msg = "Unknown result type: " + r.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}
		
	@Override
	public Result visit(Dispatcher main, IASTParameterDeclaration node) {
		ResultTypes resType = (ResultTypes) main.dispatch(node.getDeclSpecifier());
			
		mCurrentDeclaredTypes.push(resType);
		ResultDeclaration declResult = (ResultDeclaration) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return declResult;
	}
		
	@Override
	public Result visit(Dispatcher main, IASTDeclarator node) {
		CACSLLocation loc = new CACSLLocation(node);
		ResultTypes resType = mCurrentDeclaredTypes.peek();
		ResultTypes newResType = new ResultTypes(resType);
		
		newResType.isOnHeap |= ((MainDispatcher) main).getVariablesForHeap().contains(node);
		
		IASTPointerOperator[] pointerOps = node.getPointerOperators();
		for (int i = 0; i < pointerOps.length; i++) {
			newResType.cType = new CPointer(newResType.cType);
		}
		if (node instanceof IASTArrayDeclarator) {
			IASTArrayDeclarator arrDecl = (IASTArrayDeclarator) node;

			ArrayList<Expression> sizeConstants = new ArrayList<Expression>();
			Expression overallSize = new IntegerLiteral(loc, new InferredType(Type.Integer), "1");
			for (IASTArrayModifier am : arrDecl.getArrayModifiers()) {
				ResultExpression constEx = (ResultExpression) main.
						dispatch(am.getConstantExpression());
				constEx = constEx.switchToRValueIfNecessary(main, //just to be safe..
						memoryHandler, structHandler, loc);
				sizeConstants.add(constEx.lrVal.getValue());
				overallSize = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
						overallSize, constEx.lrVal.getValue(), loc);//
			}

			CArray arrayType = new CArray(
					sizeConstants.toArray(new Expression[0]), newResType.cType);
			newResType.cType = arrayType;

		} else if (node instanceof CASTFunctionDeclarator) {
			CASTFunctionDeclarator funcDecl = (CASTFunctionDeclarator) node;
			
			IASTParameterDeclaration[] paramDecls = funcDecl.getParameters();
			CDeclaration[] paramsParsed = new CDeclaration[paramDecls.length]; 
			for (int i = 0; i < paramDecls.length; i++) {
				ResultDeclaration decl = (ResultDeclaration) main.dispatch(paramDecls[i]);
				if (decl.getDeclarations().size() != 1)
					throw new UnsupportedSyntaxException(loc, "Multiple names in parameter declaration");
				if (decl.getDeclarations().get(0).getName() == ""
						&& decl.getDeclarations().get(0).getType() instanceof CPrimitive
						&& ((CPrimitive) decl.getDeclarations().get(0).getType()).getType().equals(PRIMITIVE.VOID)) {
					assert paramDecls.length == 1;
//							&& decl.getDeclarations().get(0).getType() instanceof CPrimitive 
//							&& ((CPrimitive) decl.getDeclarations().get(0).getType()).getType().equals(PRIMITIVE.VOID);
					paramsParsed = new CDeclaration[0];
					break;
				}
				paramsParsed[i] = decl.getDeclarations().get(0);
			}
			CFunction funcType = new CFunction(newResType.cType, paramsParsed);
			newResType.cType = funcType;
		} else if (node instanceof CASTDeclarator) {
			/* nothing */
		} else {
			throw new UnsupportedSyntaxException(loc, "Unknown Declarator " + node.getClass());
		}
		if (node.getNestedDeclarator() != null) {
			mCurrentDeclaredTypes.push(newResType);
			ResultDeclaration result = (ResultDeclaration) main.dispatch(node.getNestedDeclarator());
			mCurrentDeclaredTypes.pop();
			return result;
		} else {
			ResultExpression initializer = null;
			if (node.getInitializer() != null) {
				initializer = (ResultExpression) main.dispatch(node.getInitializer());
			}
			ResultDeclaration result = new ResultDeclaration();
			result.addDeclaration(newResType.cType, node.getName().toString(), initializer, newResType.isOnHeap);
			return result;
		}
	}

	@Override
	public ResultTypes checkForPointer(Dispatcher main,
			IASTPointerOperator[] pointerOps, ResultTypes resType, boolean putOnHeap) {
		if (putOnHeap || pointerOps.length != 0) {
			// TODO : not sure, if this is enough!
			// There could be multiple PointerOperators (i.e.
			// IASTPointer) - what does that mean for the translation?
			// String typeId = resType.cvar.toString();
			ASTType t = MemoryHandler.POINTER_TYPE;
			CType cvar = new CPointer(resType.cType);
			return new ResultTypes(t, resType.isConst, resType.isVoid, cvar);
		}
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
		assert rt.cType instanceof CEnum;
		CEnum cEnum = (CEnum) rt.cType;
		ILocation loc = new CACSLLocation(node);
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
			mDeclarationsGlobalInBoogie.put(cd, null);
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
			mAxioms.add(new Axiom(loc, new Attribute[0], new BinaryExpression(
					loc, Operator.COMPEQ, l, newValue)));
			symbolTable.put(fId, new SymbolTableValue(bId, cd, 
					new CDeclaration(cEnum, fId), 
					true, 
					scConstant2StorageClass(node.getDeclSpecifier().getStorageClass()))); //FIXME ??
//					staticStorageClass(node)));
		}
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		Map<VariableDeclaration, ILocation> auxVars = new HashMap<VariableDeclaration, ILocation>();
		List<Overapprox> overapprox = new ArrayList<Overapprox>();
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
			symbolTable.put(cId, new SymbolTableValue(bId, vd, new CDeclaration(null, cId), isGlobal,
//					staticStorageClass(node))); //FIXME ??
					scConstant2StorageClass(node.getDeclSpecifier().getStorageClass()))); //FIXME ??
			// initialize variable
			if (d.getInitializer() != null) {
				Result init = main.dispatch(d.getInitializer());
				assert init instanceof ResultExpression;
				ResultExpression i = (ResultExpression) init;
				decl.addAll(i.decl);
				stmt.addAll(i.stmt);
				VariableLHS lhs = new VariableLHS(loc, bId);
				AssignmentStatement assign = new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs }, new Expression[] { i.lrVal.getValue() });
				HashMap<String, IAnnotations> annots = assign.getPayload().getAnnotations();
                for (Overapprox overapprItem : overapprox) {
                    annots.put(Overapprox.getIdentifier(), overapprItem);
                }
				stmt.add(assign);
				auxVars.putAll(i.auxVars);
				overapprox.addAll(i.overappr);
			}
		}
		assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
		return new ResultExpression(stmt, null, decl, auxVars, overapprox);
	}

	private StorageClass scConstant2StorageClass(int storageClass) {
		switch (storageClass) {
		case IASTDeclSpecifier.sc_auto:
			return StorageClass.AUTO;
		case IASTDeclSpecifier.sc_extern:
			return StorageClass.EXTERN;
		case IASTDeclSpecifier.sc_mutable:
			return StorageClass.MUTABLE;
		case IASTDeclSpecifier.sc_register:
			return StorageClass.REGISTER;
		case IASTDeclSpecifier.sc_static:
			return StorageClass.STATIC;
		case IASTDeclSpecifier.sc_typedef:
			return StorageClass.TYPEDEF;
		case IASTDeclSpecifier.sc_unspecified:
			return StorageClass.UNSPECIFIED;
		default:
			throw new AssertionError("should not happen");
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTLiteralExpression node) {
		CACSLLocation loc = new CACSLLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_float_constant:
			String val = new String(node.getValue());
			val = ISOIEC9899TC3.handleFloatConstant(val, loc);
			return new ResultExpression(new RValue(new RealLiteral(loc,
					new InferredType(InferredType.Type.Real), val), new CPrimitive(PRIMITIVE.FLOAT)));
		case IASTLiteralExpression.lk_char_constant:
			val = new String(node.getValue());
			val = ISOIEC9899TC3.handleCharConstant(val, loc);
			return new ResultExpression(new RValue(new IntegerLiteral(loc,
					new InferredType(InferredType.Type.Integer), val),
					new CPrimitive(PRIMITIVE.CHAR)));
		case IASTLiteralExpression.lk_integer_constant:
			val = new String(node.getValue());
			val = ISOIEC9899TC3.handleIntegerConstant(val, loc);
			return new ResultExpression(new RValue(new IntegerLiteral(loc,
					new InferredType(InferredType.Type.Integer), val),
					new CPrimitive(PRIMITIVE.INT)));
		case IASTLiteralExpression.lk_string_literal:
			// Translate string to uninitialized char pointer
			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
			NamedType boogiePointerType = 
				new NamedType(null, new InferredType(Type.Struct), SFO.POINTER, new ASTType[0]);
            VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
                    new VarList[] { new VarList(loc, new String[] {tId}, boogiePointerType) });
            CPrimitive charType = new CPrimitive(PRIMITIVE.CHAR);
            CPointer cPointer = new CPointer(charType);
            RValue rvalue = new RValue(new IdentifierExpression(
            		loc, new InferredType(Type.Struct), tId), cPointer);
            ArrayList<Declaration> decls = new ArrayList<Declaration>();
            decls.add(tVarDecl);
    		Map<VariableDeclaration, ILocation> auxVars = 
    				new HashMap<VariableDeclaration, ILocation>(0);
    		auxVars.put(tVarDecl, loc);
			return new ResultExpression(new ArrayList<Statement>(), rvalue, decls, auxVars );
		case IASTLiteralExpression.lk_false:
			return new ResultExpression(new RValue(new BooleanLiteral(loc,
					new InferredType(InferredType.Type.Boolean), false),
					new CPrimitive(PRIMITIVE.INT)));
		case IASTLiteralExpression.lk_true:
			return new ResultExpression(new RValue(new BooleanLiteral(loc,
					new InferredType(InferredType.Type.Boolean), true),
					new CPrimitive(PRIMITIVE.INT)));
		default:
			String msg = "Unknown or unsupported kind of IASTLiteralExpression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTIdExpression node) {
		ILocation loc = new CACSLLocation(node);
		String cId = node.getName().toString();
		
		// Christian: special case: 'NULL'
		if (cId.equals("NULL")) {
		    // TODO CType is set to 'pointer to integer', is this correct...?
	        CType ctype = new CPointer(new CPrimitive(PRIMITIVE.VOID));
		    
		    return new ResultExpression(new ArrayList<Statement>(0),
	                new RValue(new IdentifierExpression(loc, SFO.NULL), ctype),
	                new ArrayList<Declaration>(0),
	                new HashMap<VariableDeclaration, ILocation>(0));
		}
		
		String bId;
		CType cType;
		boolean useHeap;
		
		// Christian: function name, handle separately
		IASTFunctionDefinition funDef =
		        ((MainDispatcher) main).getFunctionPointers().get(cId);
		if (funDef != null) {
            cType = new CPointer(new CFunction(null, null));
//		    t = new InferredType(cT);
    		bId = SFO.FUNCTION_ADDRESS + cId;
    		useHeap = true;
		}
		else {
    		bId = symbolTable.get(cId, loc).getBoogieName();
    		cType = symbolTable.get(cId, loc).getCVariable();
    		useHeap = isHeapVar(bId);
		}

		LRValue lrVal = null;
		if (useHeap) {
			IdentifierExpression idExp = new IdentifierExpression(loc, bId);
			lrVal = new HeapLValue(idExp, cType);
		} else {
			VariableLHS idLhs = new VariableLHS(loc, bId);
			lrVal = new LocalLValue(idLhs, cType);
		}
		ResultExpression result = new ResultExpression(new ArrayList<Statement>(0),
				lrVal, new ArrayList<Declaration>(0), new HashMap<VariableDeclaration,
				ILocation>(0));

		return result;
	}

	public boolean isHeapVar(String boogieId) {
		return mBoogieIdsOfHeapVars.contains(boogieId);
	}

	@Override
	public Result visit(Dispatcher main, IASTUnaryExpression node) {
		ResultExpression o = (ResultExpression) main
				.dispatch(node.getOperand());
		ILocation loc = new CACSLLocation(node);
		InferredType tInt = new InferredType(Type.Integer);
		Expression nr1 = new IntegerLiteral(loc, tInt, SFO.NR1);

		//for the cases we know that it's an RValue..
		ResultExpression rop = o.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);

		CType oType = o.lrVal.cType;
		if (oType instanceof CNamed)
			oType = ((CNamed) oType).getUnderlyingType();

		switch (node.getOperator()) {
		case IASTUnaryExpression.op_minus:
			ResultExpression ropToInt = rexToIntIfNecessary(loc, rop);
			return new ResultExpression(
					ropToInt.stmt,
					new RValue(new UnaryExpression(loc,
							ropToInt.lrVal.getValue().getType(),
							UnaryExpression.Operator.ARITHNEGATIVE, ropToInt.lrVal.getValue()), ropToInt.lrVal.cType),
							ropToInt.decl,
							ropToInt.auxVars,
							ropToInt.overappr);
		case IASTUnaryExpression.op_not:
			/** boolean <code>p</code> becomes <code>!p ? 1 : 0</code> */
			/**
			 * int <code>x</code> of form <code>y ? 1 : 0</code>
			 * becomes <code>!y ? 1 : 0</code>
			 */
			/** int <code>x</code> becomes <code>x == 0 ? 1 : 0</code> */
			ResultExpression ropToBool = rexToBoolIfNecessary(loc, rop);
			Expression negated = new UnaryExpression(loc,
					UnaryExpression.Operator.LOGICNEG,
					ropToBool.lrVal.getValue());
			ResultExpression re = new ResultExpression(
					new RValue(negated, 
							new CPrimitive(PRIMITIVE.INT), true, false),
							new HashMap<VariableDeclaration, ILocation>(),
							ropToBool.overappr);
			re.addAll(ropToBool);
			return re;
		case IASTUnaryExpression.op_plus:
			ropToInt = rexToIntIfNecessary(loc, rop);
			return new ResultExpression(ropToInt.stmt, ropToInt.lrVal, ropToInt.decl,
			        ropToInt.auxVars, ropToInt.overappr);
		case IASTUnaryExpression.op_postFixIncr:
		case IASTUnaryExpression.op_postFixDecr: {
			//FIXME: would it make sense here, to work with o, not rop??
			// --> we have to have an LValue, here, anyway.. (same thing for prefixInc/Dec)
			// --> there even is an assert below to ensure this
			assert !o.lrVal.isBoogieBool;
			// E++ -> t = E; E = t + 1; t
			ArrayList<Declaration> decl = new ArrayList<Declaration>();
			ArrayList<Statement> stmt = new ArrayList<Statement>();
			Map<VariableDeclaration, ILocation> auxVars = new HashMap<VariableDeclaration, ILocation>();
			List<Overapprox> overappr = new ArrayList<Overapprox>();
			// In this case we need a temporary variable
			String tmpName = main.nameHandler
					.getTempVarUID(SFO.AUXVAR.POST_MOD);
			ASTType tmpIType = typeHandler.ctype2asttype(loc, rop.lrVal.cType);
					
			VariableDeclaration tmpVar = 
					SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			stmt.addAll(rop.stmt);
			decl.addAll(rop.decl);
			auxVars.putAll(rop.auxVars);
			overappr.addAll(rop.overappr);
			AssignmentStatement assignStmt = new AssignmentStatement(loc,
					new LeftHandSide[] { new VariableLHS(loc, //tmpIType,
							tmpName) }, new Expression[] { rop.lrVal.getValue()});
			HashMap<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
            for (Overapprox overapprItem : overappr) {
                annots.put(Overapprox.getIdentifier(), overapprItem);
            }
            stmt.add(assignStmt);
			RValue tmpRValue = new RValue(new IdentifierExpression(loc, /*tmpIType,*/ tmpName), o.lrVal.cType);
			int op;
			if (node.getOperator() == IASTUnaryExpression.op_postFixIncr) 
				op = IASTBinaryExpression.op_plus;
			else 
				op = IASTBinaryExpression.op_minus;

			RValue rhs = null;
			if (oType instanceof CPointer)
				rhs = doPointerArith(main, op,
						loc,
						tmpRValue,
						new RValue(nr1, new CPrimitive(PRIMITIVE.INT)),
						((CPointer) tmpRValue.cType).pointsToType);
			else
				rhs = new RValue(createArithmeticExpression(op, tmpRValue.getValue(), nr1, loc), o.lrVal.cType);

			assert !(o.lrVal instanceof RValue);
			ResultExpression assign = makeAssignment(main, loc, stmt, o.lrVal, 
					rhs, decl, auxVars, overappr);//, o.lrVal.cType);
			return new ResultExpression(assign.stmt, tmpRValue, 
					assign.decl, assign.auxVars, assign.overappr);
		}
		case IASTUnaryExpression.op_prefixDecr:
		case IASTUnaryExpression.op_prefixIncr: {
			assert !o.lrVal.isBoogieBool;
			// ++E -> t = E+1; E = t; t
			ArrayList<Declaration> decl = new ArrayList<Declaration>();
			ArrayList<Statement> stmt = new ArrayList<Statement>();
			Map<VariableDeclaration, ILocation> auxVars = new HashMap<VariableDeclaration, ILocation>();
			List<Overapprox> overappr = new ArrayList<Overapprox>();
			// In this case we need a temporary variable
			String tmpName = main.nameHandler
					.getTempVarUID(SFO.AUXVAR.POST_MOD);
			ASTType tmpType = typeHandler.ctype2asttype(loc, rop.lrVal.cType);
			VariableDeclaration tmpVar = 
					SFO.getTempVarVariableDeclaration(tmpName, tmpType, loc);
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			stmt.addAll(rop.stmt);
			decl.addAll(rop.decl);
			auxVars.putAll(rop.auxVars);
			overappr.addAll(rop.overappr);
			int op;
			if (node.getOperator() == IASTUnaryExpression.op_prefixIncr) 
				op = IASTBinaryExpression.op_plus;
			else 
				op = IASTBinaryExpression.op_minus;

			RValue rhs = null;
			if (oType instanceof CPointer)
				rhs = doPointerArith(main, op,  
						loc, (RValue) o.lrVal,
						new RValue(nr1, new CPrimitive(PRIMITIVE.INT)),
						((CPointer) o.lrVal.cType).pointsToType);
			//							.lrVal.getValue();
			else
				rhs = new RValue(createArithmeticExpression(op, rop.lrVal.getValue(), nr1, loc), o.lrVal.cType);

			AssignmentStatement assignStmt = new AssignmentStatement(loc,
					new LeftHandSide[] { new VariableLHS(loc, //tmpIType,
							tmpName) }, new Expression[] { rhs.getValue() });
			HashMap<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
            for (Overapprox overapprItem : overappr) {
                annots.put(Overapprox.getIdentifier(), overapprItem);
            }
            stmt.add(assignStmt);
			assert !(o.lrVal instanceof RValue);
			RValue tmpRValue = new RValue(new IdentifierExpression(loc, /*tmpIType,*/ tmpName), o.lrVal.cType);
			ResultExpression assign = makeAssignment(main, loc, stmt, o.lrVal,
			        tmpRValue, decl, auxVars, overappr);//, o.lrVal.cType);
			return new ResultExpression(assign.stmt, tmpRValue, 
					assign.decl, assign.auxVars, assign.overappr);
		}
		case IASTUnaryExpression.op_bracketedPrimary:
			return o;
		case IASTUnaryExpression.op_sizeof:
			Map<VariableDeclaration, ILocation> emptyAuxVars =
			        new HashMap<VariableDeclaration, ILocation>(0);
			return new ResultExpression(new RValue(memoryHandler.calculateSizeOf(oType, loc),
					new CPrimitive(PRIMITIVE.INT)), emptyAuxVars);
		case IASTUnaryExpression.op_star:
		{
			Expression addr = rop.lrVal.getValue();
			if (rop.lrVal.cType instanceof CArray) {
				CArray arrayCType = (CArray) rop.lrVal.cType;
				//FIXME: type like this??
				ArrayList<Expression> dims = new ArrayList<Expression>(
						Arrays.asList(arrayCType.getDimensions()));
				dims.remove(0);
				CType newCType = null;
				if (dims.size() == 0)
					newCType = arrayCType.getValueType();
				else	
					newCType = new CArray(
							dims.toArray(new Expression[0]), arrayCType.getValueType());
				return new ResultExpression(rop.stmt, 
					new HeapLValue(addr, newCType), 
					rop.decl, 
					rop.auxVars,
					rop.overappr);
			} else {
				assert rop.lrVal.cType instanceof CPointer : "type error: expected pointer , got " + 
						rop.lrVal.cType.toString();
				return new ResultExpression(rop.stmt, 
					new HeapLValue(addr, ((CPointer)rop.lrVal.cType).pointsToType), 
					rop.decl, 
					rop.auxVars,
					rop.overappr);
			}
		}
		case IASTUnaryExpression.op_amper:
			if (o.lrVal instanceof HeapLValue) {
				Expression addr = ((HeapLValue)o.lrVal).getAddress();
				return new ResultExpression(o.stmt, new RValue(addr, new CPointer(o.lrVal.cType)), o.decl, 
						o.auxVars, o.overappr);
			} else {
				throw new AssertionError("Address of something that is not on the heap.");
			}
		case IASTUnaryExpression.op_tilde:
		    List<Overapprox> overappr = new ArrayList<Overapprox>();
		    overappr.addAll(o.overappr);
		    overappr.add(new Overapprox(Overapprox.BITVEC, loc));
            Expression bwexpr = createBitwiseExpression(node.getOperator(),
                    null, o.lrVal.getValue(), loc);
            return new ResultExpression(o.stmt, new RValue(bwexpr, o.lrVal.cType),
                    o.decl, o.auxVars, overappr);
        case IASTUnaryExpression.op_alignOf:
		default:
			String msg = "Unknown or unsupported unary operation: "
					+ node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	public ResultExpression makeAssignment(Dispatcher main, ILocation loc, ArrayList<Statement> stmt,
			LRValue lrVal, RValue rVal, ArrayList<Declaration> decl,
			Map<VariableDeclaration, ILocation> auxVars,
			List<Overapprox> overappr) {
		RValue rightHandSide = rVal;
		
		/*
		 * implicit and some explicit casts here
		 * TODO Alex+Christian: Only handles integer literals and variables.
		 * This fixes most issues, but is surely no general solution.
		 */
		CType lType = lrVal.cType.getUnderlyingType();
		CType rType = rVal.cType.getUnderlyingType();
        Expression rExpr = rVal.getValue();
		boolean convertToPointer = false;
        if (lType instanceof CPointer) {
            if (rType instanceof CPointer) {
                if (rExpr instanceof IntegerLiteral) {
                    convertToPointer = true;
                }
                else if (rExpr instanceof IdentifierExpression) {
                    String varId = ((IdentifierExpression)rExpr).getIdentifier();
                    if (symbolTable.containsBoogieSymbol(varId)) {
                        String cId = symbolTable.getCID4BoogieID(varId, loc);
                        CType cType = symbolTable.get(cId, loc).getCVariable();
                        if (cType instanceof CPrimitive &&
                                ((CPrimitive)cType).getType() == PRIMITIVE.INT) {
                            convertToPointer = true;
                        }
                    }
                }
            }
            else if (rType instanceof CPrimitive &&
                    ((CPrimitive) rType).getType() == PRIMITIVE.INT) {
                convertToPointer = true;
            }
        }
        // convert to pointer
        if (convertToPointer) {
        	if (((IntegerLiteral) rExpr).getValue().equals("0")) {
        		rightHandSide = new RValue(
            		new IdentifierExpression(loc, SFO.NULL),
                    new CPointer(new CPrimitive(PRIMITIVE.VOID)));
        	} else {
        		rightHandSide = new RValue(
        				MemoryHandler.constructPointerFromBaseAndOffset(
        						new IntegerLiteral(
        								loc, new InferredType(Type.Integer), "0"),
        								rExpr, loc),
        								new CPointer(new CPrimitive(PRIMITIVE.VOID)));
        	}
        }

		if (lrVal instanceof HeapLValue) {
			HeapLValue hlv = (HeapLValue) lrVal; 
			ResultExpression rex = new ResultExpression(memoryHandler.getWriteCall(hlv, rVal), null, 
					new ArrayList<Declaration>(), new HashMap<VariableDeclaration, ILocation>(0),
					overappr);

			stmt.addAll(rex.stmt);
			decl.addAll(rex.decl);
			auxVars.putAll(rex.auxVars);
			overappr.addAll(rex.overappr);
			
			for (String t : new String[] { SFO.INT, SFO.POINTER,
					SFO.REAL, SFO.BOOL }) {
				functionHandler.getModifiedGlobals()
				.get(functionHandler.getCurrentProcedureID())
				.add(SFO.MEMORY + "_" + t);
			}
			
			return new ResultExpression(stmt, rightHandSide, decl, auxVars, overappr);
		} else if (lrVal instanceof LocalLValue){
			LocalLValue lValue = (LocalLValue) lrVal;
			AssignmentStatement assignStmt = new AssignmentStatement(loc, new LeftHandSide[]{lValue.getLHS()}, 
					new Expression[] {rightHandSide.getValue()});
			HashMap<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
            for (Overapprox overapprItem : overappr) {
                annots.put(Overapprox.getIdentifier(), overapprItem);
            }
            stmt.add(assignStmt);

			if (!functionHandler.noCurrentProcedure())
				functionHandler.checkIfModifiedGlobal(main,
						BoogieASTUtil.getLHSId(lValue.getLHS()), loc);
//			return new ResultExpression(stmt, new RValue(lValue.getValue(), cType), decl, auxVars);
			return new ResultExpression(stmt, lValue, decl, auxVars, overappr);
		} else
			throw new AssertionError("Type error: trying to assign to an RValue in Statement" + loc.toString());
	}

	@Override
	public Result visit(Dispatcher main, IASTBinaryExpression node) {
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		Map<VariableDeclaration, ILocation> auxVars = new HashMap<VariableDeclaration, ILocation>();
		CACSLLocation loc = new CACSLLocation(node);
		List<Overapprox> overappr = new ArrayList<Overapprox>();

		ResultExpression l = (ResultExpression) main.dispatch(node.getOperand1());
		ResultExpression r = (ResultExpression) main.dispatch(node.getOperand2());

		//        assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";

		ResultExpression rl = l.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		ResultExpression rr = r.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		

		CType lType = l.lrVal.cType;
		if (lType instanceof CNamed)
			lType = ((CNamed) lType).getUnderlyingType();
		CType rType = r.lrVal.cType;
		if (rType instanceof CNamed)
			rType = ((CNamed) rType).getUnderlyingType();

		switch (node.getOperator()) {
		case IASTBinaryExpression.op_assign: {

//			if (lType instanceof CPointer  //TODO move casts to makeAssingment and function calls (maybe)
//					&& rType instanceof CPrimitive
//					&& ((CPrimitive) rType).getType() == PRIMITIVE.INT) 
//				rightSide = rrRValAsPointer;
//			else if (lType instanceof CPrimitive 
//					&& ((CPrimitive) lType).getType() == PRIMITIVE.BOOL)
//				rightSide = new RValue(main.typeHandler.convertArith2Boolean(loc, 
//						new PrimitiveType(loc, SFO.BOOL), rightSide.getValue()), lType);

			stmt.addAll(l.stmt);
			stmt.addAll(rr.stmt);
			decl.addAll(l.decl);
			decl.addAll(rr.decl);
			auxVars.putAll(l.auxVars);
			auxVars.putAll(rr.auxVars);
			overappr.addAll(l.overappr);
			overappr.addAll(rr.overappr);
			if (l.lrVal.cType instanceof CPrimitive && ((CPrimitive) l.lrVal.cType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
				ResultExpression rrToInt = rexToIntIfNecessary(loc,rr);
				return makeAssignment(main, loc, stmt, l.lrVal, (RValue) rrToInt.lrVal, decl, auxVars, overappr);//, r.lrVal.cType);
			} else {
				return makeAssignment(main, loc, stmt, l.lrVal,(RValue) rr.lrVal, decl, auxVars, overappr);//, r.lrVal.cType);
			}
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
			overappr.addAll(rl.overappr);
			overappr.addAll(rr.overappr);

			RValue rval = null;
			if (lType instanceof CPointer
					&& rType instanceof CPrimitive
					&& ((CPrimitive) rType).getType() == PRIMITIVE.INT) {
				RValue rrRValAsPointer = new RValue(MemoryHandler.constructPointerFromBaseAndOffset(
						new IntegerLiteral(loc, new InferredType(Type.Integer), "0"), 
						rr.lrVal.getValue(), loc), new CPointer(new CPrimitive(PRIMITIVE.VOID)));
				rval = new RValue(
						new BinaryExpression(loc, op, rl.lrVal.getValue(), rrRValAsPointer.getValue()),
						new CPrimitive(PRIMITIVE.INT));
			} else if (rType instanceof CPointer
					&& lType instanceof CPrimitive
					&& ((CPrimitive) lType).getType() == PRIMITIVE.INT) {
				RValue rlRValAsPointer = new RValue(MemoryHandler.constructPointerFromBaseAndOffset(
						new IntegerLiteral(loc, new InferredType(Type.Integer), "0"), 
						rl.lrVal.getValue(), loc), new CPrimitive(PRIMITIVE.VOID));
				rval = new RValue(
						new BinaryExpression(loc, op, rlRValAsPointer.getValue(), rr.lrVal.getValue()),
						new CPrimitive(PRIMITIVE.INT));
			} else {
				rval = new RValue(
						new BinaryExpression(loc, op, rl.lrVal.getValue(), rr.lrVal.getValue()),
						new CPrimitive(PRIMITIVE.INT));
			}
			rval.isBoogieBool = true;
			return new ResultExpression(stmt, 
					rval,
					decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_logicalAnd: {
			ResultExpression rlToBool = rexToBoolIfNecessary(loc, rl);
			ResultExpression rrToBool = rexToBoolIfNecessary(loc, rr);

			stmt.addAll(rlToBool.stmt);
			// NOTE: no rr.stmt
			decl.addAll(rlToBool.decl);
			decl.addAll(rrToBool.decl);
			auxVars.putAll(rlToBool.auxVars);
			auxVars.putAll(rrToBool.auxVars);
			overappr.addAll(rlToBool.overappr);
			overappr.addAll(rrToBool.overappr);

			if (rrToBool.stmt.isEmpty()) {
				// no statements in right operands, hence no side effects in operand
				// we can directly combine operands with LOGICAND
				RValue newRVal = new RValue(
						new BinaryExpression(loc, 
								BinaryExpression.Operator.LOGICAND, rlToBool.lrVal.getValue(), rrToBool.lrVal.getValue()),
						new CPrimitive(CPrimitive.PRIMITIVE.INT), true, false);
								
				
				return new ResultExpression(stmt, newRVal, decl, auxVars, overappr);
			}
			// create and add tmp var #t~AND~UID
			String resName = main.nameHandler
					.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT);
			VarList tempVar = new VarList(loc, new String[] { resName },
					new PrimitiveType(loc, SFO.BOOL));
//					new PrimitiveType(loc, SFO.INT));
			VariableDeclaration tmpVar = new VariableDeclaration(loc,
					new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			VariableLHS lhs = new VariableLHS(loc, resName);
			RValue tmpRval = new RValue(
					new IdentifierExpression(loc, resName),
					new CPrimitive(PRIMITIVE.INT), true, false);
			RValue resRval = tmpRval;
//			tmpRval = ConvExpr.toBoolean(loc, tmpRval);//FIXME: does it make sense to first create, then immediately convert it??
			// #t~AND~UID = left
		
			AssignmentStatement aStat = new AssignmentStatement(loc,
					new LeftHandSide[] { lhs }, new Expression[] { rlToBool.lrVal.getValue() });
			HashMap<String, IAnnotations> annots = aStat.getPayload().getAnnotations();
            for (Overapprox overapprItem : overappr) {
                annots.put(Overapprox.getIdentifier(), overapprItem);
            }
			stmt.add(aStat);
			// if (#t~AND~UID) {#t~AND~UID = right;}
			ArrayList<Statement> outerThenPart = new ArrayList<Statement>();
			outerThenPart.addAll(rrToBool.stmt);
            
			outerThenPart.add(new AssignmentStatement(loc,
					new LeftHandSide[] { lhs }, new Expression[] { rrToBool.lrVal.getValue() }));
			IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(),
					outerThenPart.toArray(new Statement[0]),
					new Statement[0]);
			annots = ifStatement.getPayload().getAnnotations();
            for (Overapprox overapprItem : overappr) {
                annots.put(Overapprox.getIdentifier(), overapprItem);
            }
			stmt.add(ifStatement);
			return new ResultExpression(stmt,
					resRval,
					decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_logicalOr: {
			ResultExpression rlToBool = rexToBoolIfNecessary(loc, rl);
			ResultExpression rrToBool = rexToBoolIfNecessary(loc, rr);

			stmt.addAll(rlToBool.stmt);
			// NOTE: no rr.stmt
			decl.addAll(rlToBool.decl);
			decl.addAll(rrToBool.decl);
			auxVars.putAll(rlToBool.auxVars);
			auxVars.putAll(rrToBool.auxVars);
			overappr.addAll(rlToBool.overappr);
			overappr.addAll(rrToBool.overappr);

			if (rrToBool.stmt.isEmpty()) {
				// no auxVar in operands, hence no side effects in operands
				// we can directly combine operands with LOGICOR
				return new ResultExpression(stmt,
						new RValue(new BinaryExpression(loc,
								BinaryExpression.Operator.LOGICOR,
								rlToBool.lrVal.getValue(), rrToBool.lrVal.getValue()), 
								new CPrimitive(CPrimitive.PRIMITIVE.INT),
								true, false),
								decl, auxVars, overappr);
			}
			// create and add tmp var #t~OR~UID
			String resName = main.nameHandler
					.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT);
			VarList tempVar = new VarList(loc, new String[] { resName },
					new PrimitiveType(loc, SFO.BOOL));
//					new PrimitiveType(loc, SFO.INT));
			VariableDeclaration tmpVar = new VariableDeclaration(loc,
					new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			VariableLHS lhs = new VariableLHS(loc, resName);
			RValue tmpRval = new RValue(
					new IdentifierExpression(loc, resName),
					new CPrimitive(PRIMITIVE.INT), true, false);
			RValue resRval = tmpRval;
//			tmpRval = ConvExpr.toBoolean(loc, tmpRval); //FIXME: does it make sense to first create, then immediately convert it??
			// #t~OR~UID = left
			AssignmentStatement aStat = new AssignmentStatement(loc,
					new LeftHandSide[] { lhs }, new Expression[] { rlToBool.lrVal.getValue() });
			HashMap<String, IAnnotations> annots =
			        aStat.getPayload().getAnnotations();
			for (Overapprox overapproxItem : overappr) {
			    annots.put(Overapprox.getIdentifier(), overapproxItem);
			}
			stmt.add(aStat);
			// if (#t~OR~UID) {} else {#t~OR~UID = right;}
			ArrayList<Statement> outerElsePart = new ArrayList<Statement>();
			outerElsePart.addAll(rr.stmt);
		
			outerElsePart.add(new AssignmentStatement(loc,
					new LeftHandSide[] { lhs }, new Expression[] { rrToBool.lrVal.getValue() }));
			IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(),
					new Statement[0], outerElsePart.toArray(new Statement[0]));
			annots = ifStatement.getPayload().getAnnotations();
            for (Overapprox overapprItem : overappr) {
                annots.put(Overapprox.getIdentifier(), overapprItem);
            }
            stmt.add(ifStatement);
			return new ResultExpression(stmt,
					resRval,
					decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_minus:
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide: {
			ResultExpression rlToInt = rexToIntIfNecessary(loc, rl);
			ResultExpression rrToInt = rexToIntIfNecessary(loc, rr);
			stmt.addAll(rlToInt.stmt);
			stmt.addAll(rrToInt.stmt);
			decl.addAll(rlToInt.decl);
			decl.addAll(rrToInt.decl);
			auxVars.putAll(rlToInt.auxVars);
			auxVars.putAll(rrToInt.auxVars);
            overappr.addAll(rlToInt.overappr);
            overappr.addAll(rrToInt.overappr);

			if (node.getOperator() == IASTBinaryExpression.op_divide) {
			    Check check = new Check(Check.Spec.DIVISION_BY_ZERO);
				CACSLLocation assertLoc = new CACSLLocation(node, check);
				AssertStatement assertStmt = new AssertStatement(assertLoc,
                        new BinaryExpression(assertLoc,
                                BinaryExpression.Operator.COMPNEQ,
                                new IntegerLiteral(assertLoc, SFO.NR0),
                                rrToInt.lrVal.getValue()));
				HashMap<String, IAnnotations> annots = assertStmt.getPayload().getAnnotations();
	            for (Overapprox overapprItem : overappr) {
	                annots.put(Overapprox.getIdentifier(), overapprItem);
	            }
	            stmt.add(assertStmt);
				check.addToNodeAnnot(assertStmt);
				stmt.add(assertStmt);
			}

			RValue rval = null;
			if (lType instanceof CPointer
					&& rType instanceof CPrimitive
					&& ((CPrimitive) rType).getType() == PRIMITIVE.INT) {
				rval = doPointerArith(main, node.getOperator(), 
						loc, ((RValue) rlToInt.lrVal), ((RValue) rrToInt.lrVal),
						((CPointer) rlToInt.lrVal.cType).pointsToType);
			} else if (rType instanceof CPointer
					&& lType instanceof CPrimitive
					&& ((CPrimitive) lType).getType() == PRIMITIVE.INT) {
				rval = doPointerArith(main, node.getOperator(), loc, (RValue) rrToInt.lrVal,
						(RValue) rlToInt.lrVal, ((CPointer) rrToInt.lrVal.cType).pointsToType);
			} else {
				rval = new RValue(createArithmeticExpression(
						node.getOperator(), rlToInt.lrVal.getValue(), rrToInt.lrVal.getValue(), loc), rlToInt.lrVal.cType); 
			}
			assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
			return new ResultExpression(stmt, rval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_plusAssign: {
			assert !rl.lrVal.isBoogieBool && !rr.lrVal.isBoogieBool;
			stmt.addAll(rl.stmt);
			stmt.addAll(rr.stmt);
			decl.addAll(rl.decl);
			decl.addAll(rr.decl);
			auxVars.putAll(rl.auxVars);
			auxVars.putAll(rr.auxVars);
            overappr.addAll(rl.overappr);
            overappr.addAll(rr.overappr);

			if (node.getOperator() == IASTBinaryExpression.op_divideAssign) {
			    Check check = new Check(Check.Spec.DIVISION_BY_ZERO);
				CACSLLocation assertLoc = new CACSLLocation(node, check);
				AssertStatement assertStmt = new AssertStatement(assertLoc,
                        new BinaryExpression(assertLoc,
                                BinaryExpression.Operator.COMPNEQ,
                                new IntegerLiteral(assertLoc, SFO.NR0),
                                rr.lrVal.getValue()));
				HashMap<String, IAnnotations> annots = assertStmt.getPayload().getAnnotations();
                for (Overapprox overapprItem : overappr) {
                    annots.put(Overapprox.getIdentifier(), overapprItem);
                }
				check.addToNodeAnnot(assertStmt);
				stmt.add(assertStmt);
			}
			// handle pointer arithmetic.
			RValue rightHandside = null;
			if (lType instanceof CPointer
					&& rType instanceof CPrimitive
					&& ((CPrimitive) rType).getType() == PRIMITIVE.INT) {
				rightHandside = doPointerArith(main, node.getOperator(), 
						loc, (RValue) rl.lrVal, (RValue) rr.lrVal,
						((CPointer) rl.lrVal.cType).pointsToType);
			} else {
				rightHandside = new RValue(createArithmeticExpression(node.getOperator(),
						rl.lrVal.getValue(), rr.lrVal.getValue(), loc), rr.lrVal.cType);
			}
			return makeAssignment(main, loc, stmt, l.lrVal, rightHandside,
					decl, auxVars, overappr);
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
            overappr.addAll(rl.overappr);
            overappr.addAll(rr.overappr);
            overappr.add(new Overapprox(Overapprox.BITVEC, loc));
			Expression bwexpr = createBitwiseExpression(node.getOperator(),
					rl.lrVal.getValue(), rr.lrVal.getValue(), loc);
			return new ResultExpression(stmt, new RValue(bwexpr, rl.lrVal.cType),
			        decl, auxVars, overappr);
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
            overappr.addAll(rl.overappr);
            overappr.addAll(rr.overappr);
            overappr.add(new Overapprox(Overapprox.BITVEC, loc));
			Expression bwexpr = createBitwiseExpression(
					node.getOperator(), rl.lrVal.getValue(), rr.lrVal.getValue(), loc);
			return makeAssignment(main, loc, stmt, l.lrVal, new RValue(bwexpr, rr.lrVal.cType), 
					decl, auxVars, overappr);//, l.lrVal.cType);
		}
		default:
			String msg = "Unknown or unsupported unary operation";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	private ResultExpression rexToBoolIfNecessary(ILocation loc, ResultExpression rl) {
		ResultExpression rlToBool = null;
		if (rl.lrVal.isBoogieBool) {
			rlToBool = rl;
		} else {
			rlToBool = new ResultExpression(ConvExpr.toBoolean(loc, (RValue) rl.lrVal));
			rlToBool.addAll(rl);
		}
		return rlToBool;
	}

	private ResultExpression rexToIntIfNecessary(ILocation loc, ResultExpression rl) {
		ResultExpression rlToInt = null;
		if (rl.lrVal.isBoogieBool) {
			rlToInt = new ResultExpression(ConvExpr.boolToInt(loc, (RValue) rl.lrVal));
			rlToInt.addAll(rl);
		} else {
			rlToInt = rl;
		}
		return rlToInt;
	}
	
	public RValue doPointerArith(Dispatcher main, int operator, ILocation loc,
			RValue ptr, RValue integer, CType valueType) {
	    Expression ptrAddress = ptr.getValue();
	    Expression newPointer = doPointerArith(main, operator, loc, ptrAddress, integer.getValue(), valueType);
		return new RValue(newPointer, ptr.cType);
	}
	
	
	public Expression doPointerArith(Dispatcher main, int operator, ILocation loc,
			Expression ptrAddress, Expression integer, CType valueType) {
	    Expression pointerBase = MemoryHandler.getPointerBaseAddress(ptrAddress, loc);
	    Expression pointerOffset = MemoryHandler.getPointerOffset(ptrAddress, loc);
		Expression timesSizeOf = createArithmeticExpression(IASTBinaryExpression.op_multiply, integer, 
				memoryHandler.calculateSizeOf(valueType, loc), 
				loc);
		Expression sum = createArithmeticExpression(
				operator, pointerOffset, timesSizeOf, loc);
		StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
		return newPointer;
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
	public static Expression createArithmeticExpression(int op,
			Expression left, Expression right, ILocation loc) {
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
			throw new UnsupportedSyntaxException(loc, msg);
		}
		return new BinaryExpression(loc, operator, left, right);
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
			Expression right, ILocation loc) {
	    String operatorName;
        boolean isUnary = (left == null && op == IASTUnaryExpression.op_tilde);
        if (isUnary) {
            operatorName = "bitwiseComplement";
	    }
        else {
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
    			throw new UnsupportedSyntaxException(loc, msg);
    		}
        }

		if (!this.mFunctions.containsKey(operatorName)) {
		    FunctionDeclaration d;
		    ASTType intType = new PrimitiveType(loc, SFO.INT);
		    VarList b = new VarList(loc, new String[] { "b" }, intType);
            VarList out = new VarList(loc, new String[] { "out" }, intType);
            if (isUnary) {
                d = new FunctionDeclaration(loc,
                        new Attribute[0], "~" + operatorName, new String[0],
                        new VarList[] { b }, out);
		    }
		    else {
    			VarList a = new VarList(loc, new String[] { "a" }, intType);
    			d = new FunctionDeclaration(loc,
    					new Attribute[0], "~" + operatorName, new String[0],
    					new VarList[] { a, b }, out);
		    }
		    this.mFunctions.put(operatorName, d);
		}
		Expression[] arguments = new Expression[isUnary ? 1 : 2];
		if (isUnary) {
		    arguments[0] = right;
		}
		else {
		    arguments[0] = left;
		    arguments[1] = right;
		}
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
				List<Overapprox> overappr = new ArrayList<Overapprox>();
				assert (main.isAuxVarMapcomplete(decl, rExp.auxVars));
				stmt.addAll(Dispatcher.createHavocsForAuxVars(res.auxVars)); //alex: inserted this .. why wasn't it here before???
				overappr.addAll(res.overappr);
				Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>(
						0);
				return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
			} else {
				String msg = "This statement has no effect and will be dropped: "
						+ node.getRawSignature();
				Dispatcher.warn(new CACSLLocation(node), msg);
				return new ResultSkip();
			}
		} else if (r instanceof ResultExpressionList) {
			ArrayList<Statement> stmt = new ArrayList<Statement>();
			ArrayList<Declaration> decl = new ArrayList<Declaration>();
			List<Overapprox> overappr = new ArrayList<Overapprox>();
			for (ResultExpression res : ((ResultExpressionList) r).list) {
				if (!res.stmt.isEmpty()) {
					stmt.addAll(res.stmt);
					decl.addAll(res.decl);
					assert (main.isAuxVarMapcomplete(res.decl, res.auxVars));
					stmt.addAll(Dispatcher.createHavocsForAuxVars(res.auxVars));
					overappr.addAll(res.overappr);
				}
			}
			Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>(
					0);
			return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
		} else if (r instanceof ResultSkip) {
			return r;
		}
		String msg = "We always convert to AssignmentStatement, other options raise this error!";
		ILocation loc = new CACSLLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTIfStatement node) {
		CACSLLocation loc = new CACSLLocation(node);
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		List<Overapprox> overappr = new ArrayList<Overapprox>();

		ResultExpression condResult = (ResultExpression) main.dispatch(
				node.getConditionExpression());
		condResult = condResult.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		condResult = rexToBoolIfNecessary(loc, condResult);
		RValue cond = (RValue) condResult.lrVal;
		decl.addAll(condResult.decl);
		stmt.addAll(condResult.stmt);
		overappr.addAll(condResult.overappr);
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
				throw new IncorrectSyntaxException(loc, msg);
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
				throw new IncorrectSyntaxException(loc, msg);
			}
		}
		assert thenStmt != null;
		assert elseStmt != null;
//		if (!cond.isBoogieBool) //done for condREsult already
//			cond = ConvExpr.toBoolean(loc, cond);
		// TODO : handle if(pointer), if(pointer==NULL) and if(pointer==0)
		IfStatement ifStmt = new IfStatement(loc, cond.getValue(), thenStmt.toArray(new Statement[0]),
				elseStmt.toArray(new Statement[0]));
		HashMap<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
        for (Overapprox overapprItem : overappr) {
            annots.put(Overapprox.getIdentifier(), overapprItem);
        }
        stmt.add(ifStmt);
		Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>(
				0);
		return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
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
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		CACSLLocation loc = new CACSLLocation(node);

		Result iterator = null;
		if (node instanceof IASTForStatement) {
			IASTForStatement forStmt = (IASTForStatement) node;
			// add initialization for this for loop
			IASTStatement cInitStmt = forStmt.getInitializerStatement();
			if (cInitStmt != null) {
				this.beginScope();
				Result initializer = main.dispatch(cInitStmt);
				if (initializer instanceof ResultExpression) {
					ResultExpression rExp = (ResultExpression) initializer;
					stmt.addAll(rExp.stmt);
					decl.addAll(rExp.decl);
					overappr.addAll(rExp.overappr);
				} else if (initializer instanceof ResultSkip) {
					// this is an empty statement in the C Code. We will skip it
				} else {
					String msg = "Uninplemented type of for loop initialization: "
							+ initializer.getClass();
					throw new UnsupportedSyntaxException(loc, msg);
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
				condResult = new ResultExpression(new RValue((new BooleanLiteral(loc,
						new InferredType(Type.Boolean), true)), new CPrimitive(PRIMITIVE.INT)),
						new HashMap<VariableDeclaration, ILocation>(0));

			bodyResult = main.dispatch(forStmt.getBody());
		}
		assert (main.isAuxVarMapcomplete(condResult.decl, condResult.auxVars));

		ArrayList<Statement> bodyBlock = new ArrayList<Statement>();
		if (bodyResult instanceof ResultExpression) {
			ResultExpression re = (ResultExpression) bodyResult;
			decl.addAll(re.decl);
			overappr.addAll(re.overappr);
			bodyBlock.addAll(re.stmt);
		} else if (bodyResult instanceof Result) {
			if (bodyResult.node instanceof Body) {
				Body body = (Body) (bodyResult.node);
				bodyBlock.addAll(Arrays.asList(body.getBlock()));
				decl.addAll(Arrays.asList(body.getLocalVars()));
			} else {
				String msg = "Error: unexpected dispatch result"
						+ bodyResult.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
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
				overappr.addAll(iteratorRE.overappr);
				assert (main.isAuxVarMapcomplete(iteratorRE.decl,
						iteratorRE.auxVars));
				bodyBlock.addAll(Dispatcher
						.createHavocsForAuxVars(iteratorRE.auxVars));
			} else {
				String msg = "Uninplemented type of loop iterator: "
						+ iterator.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		condResult = condResult.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		condResult = rexToBoolIfNecessary(loc, condResult);
		decl.addAll(condResult.decl);
//		RValue condRVal = ConvExpr.toBoolean(loc, (RValue) condResult.lrVal);
		RValue condRVal = (RValue) condResult.lrVal;
		IfStatement ifStmt;
		{
			Expression cond = new UnaryExpression(loc,
					UnaryExpression.Operator.LOGICNEG, condRVal.getValue());
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
					bodyBlock = functionHandler.insertMallocs(main, loc, memoryHandler, bodyBlock);
//					main.cHandler.getSymbolTable().endScope();
					for (SymbolTableValue stv : symbolTable.currentScopeValues()) 
						if (!stv.isGlobalVar()) {
//							addInitStmtsAndDecls(main, loc, decl, stmt, stv);	
							decl.add(stv.getBoogieDecl());
						}
					this.endScope();
				}
			}
			spec = specList.toArray(new LoopInvariantSpecification[0]);
			clearContract(); // take care for behavior and completeness
		}

		WhileStatement whileStmt = new WhileStatement(loc, new BooleanLiteral(loc,
                new InferredType(Type.Boolean), true), spec, bodyBlock
                .toArray(new Statement[0]));
		HashMap<String, IAnnotations> annots =
		        whileStmt.getPayload().getAnnotations();
		for (Overapprox overapprItem : overappr) {
		    annots.put(Overapprox.getIdentifier(), overapprItem);
		}
		stmt.add(whileStmt);
		Map<VariableDeclaration, ILocation> emptyAuxVars =
		        new HashMap<VariableDeclaration, ILocation>(0);
		assert (symbolTable.getActiveScopeNum() == scopeDepth);
		return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
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
				rex = rex.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
				result.list.add(new ResultExpressionListRec(rex.stmt, rex.lrVal,
						rex.decl, rex.auxVars, rex.overappr));
				result.auxVars.putAll(((ResultExpression) r).auxVars);
			} else {
				String msg = "Unexpected result";
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}
		return result;
	}

	@Override
	public Result visit(Dispatcher main, CASTDesignatedInitializer node) {
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
		Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>();
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
		Map<VariableDeclaration, ILocation> auxVars = new HashMap<VariableDeclaration, ILocation>();
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		Result switchParam = main.dispatch(node.getControllerExpression());
		assert switchParam instanceof ResultExpression;
		ResultExpression l = ((ResultExpression) switchParam).switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		stmt.addAll(l.stmt);
		decl.addAll(l.decl);
		auxVars.putAll(l.auxVars);
		overappr.addAll(l.overappr);
		Expression switchArg = l.lrVal.getValue();
    
		Expression cond = null;
		boolean isFirst = true;
		String breakLabelName = "SWITCH~BREAK~" + node.hashCode();

		ArrayList<Statement> ifBlock = new ArrayList<Statement>();
		this.beginScope();
		for (IASTNode child : node.getBody().getChildren()) {
			CACSLLocation locC = new CACSLLocation(child);
			if (isFirst
					&& !(child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement)) {
				String msg = "A case/default statement is expected at the beginning of a switch block!";
				throw new IncorrectSyntaxException(locC, msg);
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
						HashMap<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
		                for (Overapprox overapprItem : res.overappr) {
		                    annots.put(Overapprox.getIdentifier(), overapprItem);
		                }
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
				overappr.addAll(res.overappr);
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
			HashMap<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
            for (Overapprox overapprItem : overappr) {
                annots.put(Overapprox.getIdentifier(), overapprItem);
            }
			stmt.add(ifStmt);
		}
		checkForACSL(main, stmt, null, node);
		stmt.add(new Label(loc, breakLabelName));
		stmt.addAll(Dispatcher.createHavocsForAuxVars(auxVars));
		Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>(
				0);
		return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTCaseStatement node) {
		ResultExpression c = (ResultExpression) main.dispatch(node
				.getExpression());
		return c.switchToRValueIfNecessary(main, memoryHandler, structHandler, new CACSLLocation(node));
	}

	@Override
	public Result visit(Dispatcher main, IASTDefaultStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>(
				0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		return new ResultExpression(stmt, 
				new RValue(new BooleanLiteral(new CACSLLocation(node), new InferredType(Type.Boolean), true), 
						new CPrimitive(PRIMITIVE.INT)), 
				decl, emptyAuxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTLabelStatement node) {
		ILocation loc = new CACSLLocation(node);
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>(
				0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		String label = node.getName().toString();
		if (mErrorLabelWarning && label.equals("ERROR")) {
			String longDescription =  "The label \"ERROR\" does not have a special meaning in the translation mode you selected. You might want to change your settings and use the SV-COMP translation mode.";  
			Dispatcher.warn(loc, longDescription);
		}
		stmt.add(new Label(loc, label));
		Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ResultExpression) {
			ResultExpression res = (ResultExpression) r;
			decl.addAll(res.decl);
			stmt.addAll(res.stmt);
			overappr.addAll(res.overappr);
			return new ResultExpression(stmt, res.lrVal, decl, emptyAuxVars,
			        overappr);
		} else if (r instanceof ResultSkip) {
			return new ResultExpression(stmt, null, decl, emptyAuxVars);
		} else { // r instanceof Result ...
			RValue expr = null;
			if (r.node instanceof Statement) {
				stmt.add((Statement) r.node);
			} else if (r.node instanceof Declaration) {
				decl.add((Declaration) r.node);
			} else if (r.node instanceof Expression) {
				expr = new RValue((Expression) r.node, null);//FIXME ??
			} else if (r.node instanceof Body) {
				// we already have a unique naming for variables! --> unfold
				Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				String msg = "Unexpected boogie AST node type: "
						+ r.node.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ResultExpression(stmt, expr, decl, emptyAuxVars);
		}
	}

	public Result handleLabelCommonCode(Dispatcher main, IASTLabelStatement node, ILocation loc) {

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>(
				0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		String label = node.getName().toString();
		stmt.add(new Label(loc, label));
		Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ResultExpression) {
			ResultExpression res = (ResultExpression) r;
			decl.addAll(res.decl);
			stmt.addAll(res.stmt);
			overappr.addAll(res.overappr);
			return new ResultExpression(stmt, res.lrVal, decl, emptyAuxVars,
			        overappr);
		} else if (r instanceof ResultSkip) {
			return new ResultExpression(stmt, null, decl, emptyAuxVars,
			        overappr);
		} else { // r instanceof Result ...
			RValue expr = null;
			if (r.node instanceof Statement) {
				stmt.add((Statement) r.node);
			} else if (r.node instanceof Declaration) {
				decl.add((Declaration) r.node);
			} else if (r.node instanceof Expression) {
				expr = new RValue((Expression) r.node, null); //FIXME ??
			} else if (r.node instanceof Body) {
				// we already have a unique naming for variables! --> unfold
				Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				String msg = "Unexpected boogie AST node type: "
						+ r.node.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ResultExpression(stmt, expr, decl, emptyAuxVars,
			        overappr);
		}
	}


	@Override
	public Result visit(Dispatcher main, IASTGotoStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		String[] name = new String[] { node.getName().toString() };
		stmt.add(new GotoStatement(new CACSLLocation(node), name));
		Map<VariableDeclaration, ILocation> emptyAuxVars = new HashMap<VariableDeclaration, ILocation>(
				0);
		return new ResultExpression(stmt, null, new ArrayList<Declaration>(),
				emptyAuxVars);
	}

	@Override
	public Result visit(Dispatcher main, IASTCastExpression node) {
		ResultExpression expr = (ResultExpression) main.dispatch(node.getOperand());
        ILocation loc = new CACSLLocation(node);
		expr = expr.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		
		//TODO: check validity of cast?
		
		ResultTypes resTypes = (ResultTypes) main.dispatch(node.getTypeId().getDeclSpecifier());
		int noPtrOps = node.getTypeId().getAbstractDeclarator().getPointerOperators().length; //FIXME: ??
		
		CType newCType = resTypes.cType;
		for (int i = 0; i < noPtrOps; i++) 
			newCType = new CPointer(newCType);
		
		// cast pointer -> integer/other pointer
		CType underlyingType = expr.lrVal.cType.getUnderlyingType();
		if (underlyingType instanceof CPointer) {
		    // cast from pointer to integer
		    if (newCType instanceof CPrimitive &&
		            ((CPrimitive)newCType).getType() == PRIMITIVE.INT) {
		        Expression e = MemoryHandler.getPointerOffset(expr.lrVal.getValue(), loc);
		        expr.lrVal = new RValue(e, newCType);
		    }
		    // cast from pointer to pointer is ignored
		    else if (!(newCType.getUnderlyingType() instanceof CPointer)) {
                throw new UnsupportedSyntaxException(loc,
                        "Explicit cast from pointer not supported.");
            }
		}
		// cast integer -> pointer
		else if (underlyingType instanceof CPrimitive) {
		    CPrimitive cprim = (CPrimitive)underlyingType;
		    if (cprim.getType() == PRIMITIVE.INT &&
		            newCType instanceof CPointer) {
		        Expression e = MemoryHandler.constructPointerFromBaseAndOffset(
		                new IntegerLiteral(loc, "0"), expr.lrVal.getValue(), loc);
		        expr.lrVal = new RValue(e, newCType);
		    }
		}
		
		expr.lrVal.cType = newCType;
		expr.lrVal.getValue().setType(new InferredType(newCType));
		
//		String msg = "Ignored cast! At line: "
//				+ node.getFileLocation().getStartingLineNumber();
//		Dispatcher.unsoundnessWarning(loc, msg,
//				"Ignored cast!");
		return expr;
	}

	@Override
	public Result visit(Dispatcher main, IASTConditionalExpression node) {
		ILocation loc = new CACSLLocation(node);
		assert node.getChildren().length == 3;
		Result resLocCond = main.dispatch(node.getLogicalConditionExpression());
		assert resLocCond instanceof ResultExpression;
		ResultExpression reLocCond = (ResultExpression) resLocCond;
		reLocCond = reLocCond.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		reLocCond = rexToBoolIfNecessary(loc, reLocCond);

		Result rPositive = main.dispatch(node.getPositiveResultExpression());
		assert rPositive instanceof ResultExpression;
		ResultExpression rePositive = (ResultExpression) rPositive;
		rePositive = rePositive.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);

		Result rNegative = main.dispatch(node.getNegativeResultExpression());
		assert rNegative instanceof ResultExpression;
		ResultExpression reNegative = (ResultExpression) rNegative;
		reNegative = reNegative.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = 
				new HashMap<VariableDeclaration, ILocation>(0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		decl.addAll(reLocCond.decl);
		stmt.addAll(reLocCond.stmt);
		overappr.addAll(reLocCond.overappr);
		String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.ITE);
		ASTType tmpType = typeHandler.ctype2asttype(loc, rePositive.lrVal.cType);
		VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpType, loc);
		decl.add(tmpVar);
		RValue condition = (RValue) reLocCond.lrVal;
//		condition = ConvExpr.toBoolean(loc, condition); //done for relocCond
		List<Statement> ifStatements = new ArrayList<Statement>();
		{
			ifStatements.addAll(rePositive.stmt);
			LeftHandSide[] lhs = { new VariableLHS(loc, tmpName) };
			AssignmentStatement assignStmt = new AssignmentStatement(loc, lhs, 
					new Expression[] { rePositive.lrVal.getValue() });
			HashMap<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
            for (Overapprox overapprItem : overappr) {
                annots.put(Overapprox.getIdentifier(), overapprItem);
            }
			ifStatements.add(assignStmt);
			List<HavocStatement> havocAuxVars = Dispatcher
					.createHavocsForAuxVars(rePositive.auxVars);
			ifStatements.addAll(havocAuxVars);
			decl.addAll(rePositive.decl);
			overappr.addAll(rePositive.overappr);
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
			overappr.addAll(reNegative.overappr);
		}
		Statement ifStatement = new IfStatement(loc, condition.getValue(), 
				ifStatements.toArray(new Statement[0]), 
				elseStatements.toArray(new Statement[0]));
		HashMap<String, IAnnotations> annots = ifStatement.getPayload().getAnnotations();
		for (Overapprox overapprItem : overappr) {
            annots.put(Overapprox.getIdentifier(), overapprItem);
        }
		stmt.add(ifStatement);

		IdentifierExpression tmpExpr = new IdentifierExpression(loc, tmpName);
		List<HavocStatement> havocAuxVars = Dispatcher
				.createHavocsForAuxVars(reLocCond.auxVars);
		stmt.addAll(havocAuxVars);
		auxVars.put(tmpVar,loc);
		assert rePositive.lrVal.cType.equals(reNegative.lrVal.cType);
		return new ResultExpression(stmt, new RValue(tmpExpr,
		        rePositive.lrVal.cType), decl, auxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTArraySubscriptExpression node) {
		return arrayHandler.handleArraySubscriptExpression(main, memoryHandler, structHandler, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTInitializerClause node) {
		assert node.getChildren().length == 1;
		Result r = main.dispatch(node.getChildren()[0]);
		assert r instanceof ResultExpression;
		ResultExpression rex = (ResultExpression) r;
		return rex.switchToRValueIfNecessary(main, memoryHandler, structHandler, new CACSLLocation(node));
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
		ILocation loc = new CACSLLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemDeclaration node) {
		String msg = "Syntax error (declaration problem) in C program: "
				+ node.getProblem().getMessage();
		ILocation loc = new CACSLLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemExpression node) {
		String msg = "Syntax error (expression problem) in C program: "
				+ node.getProblem().getMessage();
		ILocation loc = new CACSLLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblem node) {
		String msg = "Syntax error in C program: " + node.getMessage();
		ILocation loc = new CACSLLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemTypeId node) {
		String msg = "Syntax error (type ID problem) in C program: "
				+ node.getProblem().getMessage();
		ILocation loc = new CACSLLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTTypeIdExpression node) {
		ILocation loc = new CACSLLocation(node);
		switch (node.getOperator()) {
		case IASTTypeIdExpression.op_sizeof:
			ResultTypes rt = (ResultTypes) main.dispatch(
					node.getTypeId().getDeclSpecifier());
			ResultTypes checked = checkForPointer(main, node.getTypeId().
					getAbstractDeclarator().getPointerOperators(), rt, false);
			return new ResultExpression(new RValue(memoryHandler.
					calculateSizeOf(checked.cType, loc), new CPrimitive(PRIMITIVE.INT)));
		default:
			break;
		}
		String msg = "Unsupported boogie AST node type: " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	/**
	 * m_declarationsGlobalInBoogie may contain type declarations that 
	 * stem from typedefs using an incomplete struct type. This method
	 * is called when the struct type is completed.
	 * @param cvar 
	 * @param incompleteStruct 
	 */
	public void completeTypeDeclaration(CStruct incompleteStruct, CStruct cvar) {
		assert incompleteStruct.isIncomplete();
		TypeDeclaration oldDec = null;
		CDeclaration oldCDec = null;
		TypeDeclaration newDec = null;
		for (Entry<Declaration, CDeclaration> en : mDeclarationsGlobalInBoogie.entrySet()) {
			if (en.getValue().getType().toString().equals(incompleteStruct.toString())) {
				oldDec = (TypeDeclaration) en.getKey();
				oldCDec = en.getValue();
				newDec = new TypeDeclaration(oldDec.getLocation(), oldDec.getAttributes(),
						oldDec.isFinite(), oldDec.getIdentifier(), oldDec.getTypeParams(),
						typeHandler.ctype2asttype(oldDec.getLocation(), cvar));
				break; //the if should be entered only once, anyway
			}
		}
		if (oldDec != null) {
			mDeclarationsGlobalInBoogie.remove(oldDec);
			mDeclarationsGlobalInBoogie.put(newDec, oldCDec);
		}
	}

	/**
	 * @param bId Boogie ID
	 */
	public void addBoogieIdsOfHeapVars(String bId) {
	    mBoogieIdsOfHeapVars.add(bId);
	}

	@Override
	public SymbolTable getSymbolTable() {
		return symbolTable;
	}

	@Override
	public void clearContract() {
		this.contract.clear();
	}

	//commented out the uses of this in CompositeTypeSpecifier, EnumerationSpecifier, SimpleDeclSpecifier
	//because calculatesizeOf is executed when it's needed and that's all we want, right?
	@Override
	public void addSizeOfConstants(CType cvar, ILocation loc) {
		memoryHandler.calculateSizeOf(cvar, loc);
	}
	
	public static Expression getInitExpr(CType cType) {
		CType ut = cType.getUnderlyingType();
		InferredType it = new InferredType(ut);
		
		if (ut instanceof CPrimitive) {
			switch (((CPrimitive) ut).getType()) {
			case CHAR:
			case CHAR16:
			case CHAR32:
			case WCHAR:
			case INT:
				return new IntegerLiteral(null, it, SFO.NR0);
			case DOUBLE:
			case FLOAT:
				return new RealLiteral(null, it, SFO.NR0F);
			case VOID:
				default:
				throw new AssertionError("unknown type to init");
			}
		} else if (ut instanceof CPointer) {
			return new IdentifierExpression(null, it, SFO.NULL);
		} else if (ut instanceof CArray) {
				throw new AssertionError("wrong type to init");
		} else if (ut instanceof CStruct) {
				throw new AssertionError("wrong type to init");
		} else {
				throw new AssertionError("wrong type to init");
		}
	}
	
	public static Expression convertLHSToExpression(LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return new IdentifierExpression(lhs.getLocation(), lhs.getType(),
					((VariableLHS) lhs).getIdentifier());
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS alhs = (ArrayLHS) lhs;
			Expression array = convertLHSToExpression(alhs.getArray());
			return new ArrayAccessExpression(alhs.getLocation(), alhs.getType(), array,
					alhs.getIndices());
		} else if (lhs instanceof StructLHS) {
			StructLHS slhs = (StructLHS) lhs;
			Expression struct = convertLHSToExpression(slhs.getStruct());
			return new StructAccessExpression(slhs.getLocation(), slhs.getType(), struct,
					slhs.getField());
		} else {
			throw new AssertionError("Strange LeftHandSide " + lhs);
		}
	}
	
	public void beginScope() {
		this.typeHandler.beginScope();
		this.symbolTable.beginScope();
		this.functionHandler.getMallocedAuxPointers().beginScope();
	}
	
	public void endScope() {
		this.typeHandler.endScope();
		this.symbolTable.endScope();
		this.functionHandler.getMallocedAuxPointers().endScope();
	}

	@Override
	public void addSizeOfConstants(CType cvar) {
		// this is here only because eclipse really wants this method and I don't know why..
		throw new AssertionError();
	}
}
