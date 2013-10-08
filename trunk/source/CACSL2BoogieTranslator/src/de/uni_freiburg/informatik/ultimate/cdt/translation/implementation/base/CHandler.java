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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
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
    protected MemoryHandler memoryHandler;
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
        Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
        if (node.getDeclarators() != null && node.getDeclarators().length > 0) {
            // we decide on the first declarator ... [0] does NOT mean, that
            // only the first declarator is handled!
            IASTDeclarator cDecl = node.getDeclarators()[0];
            if (cDecl instanceof IASTFunctionDeclarator) {
                return functionHandler.handleFunctionDeclaration(main,
                        contract, node);
            } else if (cDecl instanceof IASTArrayDeclarator) {
                return arrayHandler.handleArrayDeclaration(main, structHandler,
                        node, globalVariables, globalVariablesInits);
            }
            if (node.getDeclSpecifier() == null) {
                String msg = "This statement can be removed!";
                Dispatcher.unsoundnessWarning(loc, msg, "empty!");
                return new ResultSkip();
            }
        }
        if (node.getDeclSpecifier() instanceof IASTEnumerationSpecifier) {
            return handleEnumDeclaration(main, node);
        }
        // Here we handle "normal variable" declaration, all other cases
        // should be caught before
        Result r = main.dispatch(node.getDeclSpecifier());
        assert r instanceof ResultSkip || r instanceof ResultTypes;
        if (r instanceof ResultSkip)
            return r;
        if (r instanceof ResultTypes) {
            ResultTypes resType = (ResultTypes) r;
            Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                    0);
            ResultExpression result = new ResultExpression(null, emptyAuxVars);
            ResultExpression staticVarStorage = new ResultExpression(null,
                    emptyAuxVars);
            boolean isGlobal = node.getParent() == node.getTranslationUnit();
            if (node.getParent() == node.getTranslationUnit()) {
                result.decl.addAll(resType.typeDeclarations);
            } else if (!resType.typeDeclarations.isEmpty()) {
                // FIXME : check if typedef can occur locally at all!
                String msg = "Unexpected location for a typedef!";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
            for (IASTDeclarator d : node.getDeclarators()) {
                String cId = d.getName().getRawSignature();
                // Get the type of this variable
                assert resType.getType() != null;
                String bId = main.nameHandler.getUniqueIdentifier(node, cId,
                        symbolTable.getCompoundCounter());
                if (main.typeHandler.isStructDeclaration()) {
                    // store C variable information into this result, as this is
                    // a struct field! We need this information to build the
                    // structs C variable information recursively.
                    assert resType.cvar != null;
                    result.declCTypes.add(resType.cvar);
                }
                ResultTypes checkedType = checkForPointer(main,
                        d.getPointerOperators(), resType);
                ASTType type = checkedType.getType();
                CType cvar = checkedType.cvar;
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
                // Handle initializer clause
                if (d.getInitializer() != null) {
                    if (type instanceof StructType) {
                        Result initializer = main.dispatch(d.getInitializer());
                        assert initializer instanceof ResultExpressionListRec;
                        ResultExpressionListRec relr = ((ResultExpressionListRec) initializer);
                        VariableLHS lhs = new VariableLHS(loc,
                                new InferredType(type), bId);
                        if (cvar instanceof CNamed) {
                            cvar = ((CNamed) cvar).getUnderlyingType();
                        }
                        assert cvar instanceof CStruct;
                        ResultExpression init = structHandler.handleStructInit(
                                main, arrayHandler, loc, (StructType) type,
                                (CStruct) cvar, lhs, relr,
                                new ArrayList<Integer>(), -1);
                        auxVars.putAll(init.auxVars);
                        assert init.expr == null && init.decl.isEmpty();
                        if (resType.cvar.isStatic() && !isGlobal) {
                            staticVarStorage.stmt.addAll(init.stmt);
                        } else {
                            result.stmt.addAll(init.stmt);
                        }
                    } else { // it should be a "normal variable"
                        ResultExpression rExpr = ((ResultExpression) (main
                                .dispatch(d.getInitializer())));
                        auxVars.putAll(rExpr.auxVars);
                        rExpr.expr = main.typeHandler.convertArith2Boolean(
                                loc, type, rExpr.expr);
                        Expression[] rhs = new Expression[] { rExpr.expr };
                        VariableLHS[] lhs = new VariableLHS[] { new VariableLHS(
                                loc, bId) };
                        AssignmentStatement as = new AssignmentStatement(loc,
                                lhs, rhs);
                        // TODO: Ask Markus where I should havoc temp aux vars.
                        if (resType.cvar.isStatic() && !isGlobal) {
                            staticVarStorage.decl.addAll(rExpr.decl);
                            staticVarStorage.stmt.addAll(rExpr.stmt);
                            staticVarStorage.stmt.add(as);
                        } else {
                            result.decl.addAll(rExpr.decl);
                            result.stmt.addAll(rExpr.stmt);
                            result.stmt.add(as);
                        }
                    }
                } else if (!cvar.isGlobalVariable() && !cvar.isStatic()) {
                    // if not initialized directly and if not global and not
                    // static. This is required, since this variable could be
                    // within a loop and needs to be havoc'ed to represent C's
                    // behavior!
                    result.stmt.add(new HavocStatement(loc,
                            new String[] { bId }));
                }
            }
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
                cEnum.getIdentifier(), symbolTable.getCompoundCounter());
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
                newValue = rex.expr;
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
                    symbolTable.getCompoundCounter());
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
                        new LeftHandSide[] { lhs }, new Expression[] { i.expr }));
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
                return new ResultExpression(new RealLiteral(loc,
                        new InferredType(InferredType.Type.Real), val), auxVars);
            case IASTLiteralExpression.lk_char_constant:
                val = new String(node.getValue());
                val = ISOIEC9899TC3.handleCharConstant(val, loc);
                assert val.length() == 3;
                assert val.startsWith("'");
                assert val.endsWith("'");
                val = SFO.EMPTY + (int) val.charAt(1);
                return new ResultExpression(new IntegerLiteral(loc,
                        new InferredType(InferredType.Type.Integer), val),
                        auxVars);
            case IASTLiteralExpression.lk_integer_constant:
                val = new String(node.getValue());
                val = ISOIEC9899TC3.handleIntegerConstant(val, loc);
                return new ResultExpression(new IntegerLiteral(loc,
                        new InferredType(InferredType.Type.Integer), val),
                        auxVars);
            case IASTLiteralExpression.lk_string_literal:
                // TODO : StringLiteral is not correct - we need a char[]...
                return new ResultExpression(new StringLiteral(loc,
                        new InferredType(InferredType.Type.String), new String(
                                node.getValue())), auxVars);
            case IASTLiteralExpression.lk_false:
                return new ResultExpression(new BooleanLiteral(loc,
                        new InferredType(InferredType.Type.Boolean), false),
                        auxVars);
            case IASTLiteralExpression.lk_true:
                return new ResultExpression(new BooleanLiteral(loc,
                        new InferredType(InferredType.Type.Boolean), true),
                        auxVars);
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
        ResultExpression result = new ResultExpression(
                new IdentifierExpression(loc, t, bId),
                new HashMap<VariableDeclaration, CACSLLocation>(0));
        result.cType = symbolTable.get(cId, loc).getCVariable();
        return result;
    }
    
    @Override
    public Result visit(Dispatcher main, IASTUnaryExpression node) {
        ResultExpression o = (ResultExpression) main
                .dispatch(node.getOperand());
        CACSLLocation loc = new CACSLLocation(node);
        InferredType tBool = new InferredType(InferredType.Type.Boolean);
        InferredType tInt = new InferredType(Type.Integer);
        Expression nr1 = new IntegerLiteral(loc, tInt, SFO.NR1);
        switch (node.getOperator()) {
            case IASTUnaryExpression.op_minus:
                return new ResultExpression(new UnaryExpression(loc,
                        o.expr.getType(),
                        UnaryExpression.Operator.ARITHNEGATIVE, o.expr),
                        o.auxVars);
            case IASTUnaryExpression.op_not:
            	InferredType iType = (InferredType) o.expr.getType();
            	// boolean <code>p</code> becomes <code>!p ? 1 : 0</code>
            	if (iType.getType() == InferredType.Type.Boolean) {
                    return new ResultExpression(o.stmt,
                    		wrapBoolean2Int(loc, new UnaryExpression(loc,
                    				UnaryExpression.Operator.LOGICNEG, o.expr)),
                    		o.decl, o.auxVars);
            	} else if (iType.getType() == InferredType.Type.Integer) {
            		// unwrap if possible
            		if (main.typeHandler instanceof TypeHandler) {
            			final Expression unwrapped =
            					((TypeHandler)main.typeHandler).
            							unwrapInt2Boolean(o.expr);
            			if (unwrapped != null) {
            				/*
            				 * int <code>x</code> of form <code>y ? 1 : 0</code>
            				 * becomes <code>!y ? 1 : 0</code>
            				 */
            				return new ResultExpression(o.stmt,
            						wrapBoolean2Int(loc,
            								new UnaryExpression(loc,
                            				UnaryExpression.Operator.LOGICNEG,
                            				unwrapped)),
            						o.decl, o.auxVars);
            			}
            		}
            		
            		// int <code>x</code> becomes <code>x == 0 ? 1 : 0</code>
            		return new ResultExpression(o.stmt,
            				wrapBinaryBoolean2Int(loc,
            						BinaryExpression.Operator.COMPEQ, o.expr,
            						new IntegerLiteral(loc, tInt, SFO.NR0)),
            				o.decl, o.auxVars);
            	} else {
            		throw new UnsupportedOperationException(
            				"only bool and int at the moment");
            	}
            case IASTUnaryExpression.op_plus:
                return new ResultExpression(o.stmt, o.expr, o.decl, o.auxVars);
            case IASTUnaryExpression.op_postFixIncr:
            case IASTUnaryExpression.op_postFixDecr:
                // E++ -> t = E; E = E + 1; t
                ArrayList<Declaration> decl = new ArrayList<Declaration>();
                ArrayList<Statement> stmt = new ArrayList<Statement>();
                Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
                // In this case we need a temporary variable
                String tmpName = main.nameHandler
                        .getTempVarUID(SFO.AUXVAR.POST_MOD);
                InferredType tmpIType = (InferredType) o.expr.getType();
                VariableDeclaration tmpVar = 
                		SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
                auxVars.put(tmpVar, loc);
                decl.add(tmpVar);
                stmt.addAll(o.stmt);
                decl.addAll(o.decl);
                stmt.add(new AssignmentStatement(loc,
                        new LeftHandSide[] { new VariableLHS(loc, tmpIType,
                                tmpName) }, new Expression[] { o.expr }));
                LeftHandSide lhs = BoogieASTUtil.getLHSforExpression(o.expr);
                BinaryExpression.Operator op;
                if (node.getOperator() == IASTUnaryExpression.op_postFixIncr) {
                    op = BinaryExpression.Operator.ARITHPLUS;
                } else {
                    op = BinaryExpression.Operator.ARITHMINUS;
                }
                Expression[] rhs = new Expression[] { new BinaryExpression(loc,
                        tInt, op, o.expr, nr1) };
                IASTNode operand = node.getOperand();
                if (operand instanceof IASTUnaryExpression
                        && ((IASTUnaryExpression) operand).getOperator() == IASTUnaryExpression.op_bracketedPrimary
                        && ((IASTUnaryExpression) operand).getOperand() instanceof IASTUnaryExpression)
                    operand = ((IASTUnaryExpression) operand).getOperand();
                if (operand instanceof IASTUnaryExpression
                        && ((IASTUnaryExpression) operand).getOperator() == IASTUnaryExpression.op_star) {
                    ResultExpression myOperand = (ResultExpression) main
                            .dispatch(((IASTUnaryExpression) operand)
                                    .getOperand());
                    stmt.addAll(myOperand.stmt);
                    decl.addAll(myOperand.decl);
                    auxVars.putAll(myOperand.auxVars);
                    ResultExpression rex = memoryHandler.getWriteCall(
                            myOperand.expr, rhs[0]);
                    stmt.addAll(rex.stmt);
                    decl.addAll(rex.decl);
                    auxVars.putAll(rex.auxVars);
                    for (String t : new String[] { SFO.INT, SFO.POINTER,
                            SFO.REAL, SFO.BOOL }) {
                        functionHandler.getModifiedGlobals()
                                .get(functionHandler.getCurrentProcedureID())
                                .add(SFO.MEMORY + "_" + t);
                    }
                } else if (tmpIType instanceof InferredType
                        && ((InferredType) tmpIType).getType() == Type.Pointer) {
                    ResultExpression ptrMan = memoryHandler.manipulatePointer(
                            o.expr, op, nr1);
                    stmt.addAll(ptrMan.stmt);
                    decl.addAll(ptrMan.decl);
                    auxVars.putAll(ptrMan.auxVars);
                } else {
                    functionHandler.checkIfModifiedGlobal(main,
                            BoogieASTUtil.getLeftMostId(o.expr), loc);
                    stmt.add(new AssignmentStatement(loc,
                            new LeftHandSide[] { lhs }, rhs));
                }
                return new ResultExpression(stmt, new IdentifierExpression(loc,
                        tmpIType, tmpName), decl, auxVars);
            case IASTUnaryExpression.op_prefixDecr:
            case IASTUnaryExpression.op_prefixIncr:
                // ++E -> E = E+1; E
                if (node.getOperator() == IASTUnaryExpression.op_prefixIncr) {
                    op = BinaryExpression.Operator.ARITHPLUS;
                } else {
                    op = BinaryExpression.Operator.ARITHMINUS;
                }
                stmt = new ArrayList<Statement>();
                decl = new ArrayList<Declaration>();
                auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
                operand = node.getOperand();
                if (operand instanceof IASTUnaryExpression
                        && ((IASTUnaryExpression) operand).getOperator() == IASTUnaryExpression.op_bracketedPrimary
                        && ((IASTUnaryExpression) operand).getOperand() instanceof IASTUnaryExpression)
                    operand = ((IASTUnaryExpression) operand).getOperand();
                if (operand instanceof IASTUnaryExpression
                        && ((IASTUnaryExpression) operand).getOperator() == IASTUnaryExpression.op_star) {
                    ResultExpression myOperand = (ResultExpression) main
                            .dispatch(((IASTUnaryExpression) operand)
                                    .getOperand());
                    stmt.addAll(myOperand.stmt);
                    decl.addAll(myOperand.decl);
                    auxVars.putAll(myOperand.auxVars);
                    stmt.addAll(o.stmt);
                    decl.addAll(o.decl);
                    auxVars.putAll(o.auxVars);
                    rhs = new Expression[] { new BinaryExpression(loc, tInt,
                            Operator.ARITHPLUS, o.expr, nr1) };
                    ResultExpression rex = memoryHandler.getWriteCall(
                            myOperand.expr, rhs[0]);
                    stmt.addAll(rex.stmt);
                    decl.addAll(rex.decl);
                    auxVars.putAll(rex.auxVars);
                    for (String t : new String[] { SFO.INT, SFO.POINTER,
                            SFO.REAL, SFO.BOOL }) {
                        functionHandler.getModifiedGlobals()
                                .get(functionHandler.getCurrentProcedureID())
                                .add(SFO.MEMORY + "_" + t);
                    }
                    ResultExpression read = memoryHandler.getReadCall(main,
                            tInt, myOperand.expr);
                    decl.addAll(read.decl);
                    stmt.addAll(read.stmt);
                    auxVars.putAll(read.auxVars);
                    return new ResultExpression(stmt, read.expr, decl, auxVars);
                }
                if (o.expr.getType() instanceof InferredType
                        && ((InferredType) o.expr.getType()).getType() == Type.Pointer) {
                    ResultExpression ptrMan = memoryHandler.manipulatePointer(
                            o.expr, op, nr1);
                    stmt.addAll(ptrMan.stmt);
                    decl.addAll(ptrMan.decl);
                    auxVars.putAll(ptrMan.auxVars);
                } else {
                    rhs = new Expression[] { new BinaryExpression(loc, tInt,
                            op, o.expr, nr1) };
                    stmt.add(new AssignmentStatement(loc,
                            new LeftHandSide[] { BoogieASTUtil
                                    .getLHSforExpression(o.expr) }, rhs));
                }
                functionHandler.checkIfModifiedGlobal(main,
                        BoogieASTUtil.getLeftMostId(o.expr), loc);
                return new ResultExpression(stmt, o.expr, decl, auxVars);
            case IASTUnaryExpression.op_bracketedPrimary:
                return o;
            case IASTUnaryExpression.op_sizeof:
                Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                        0);
                return new ResultExpression(memoryHandler.getSizeOf(main,
                        node.getOperand()), emptyAuxVars);
            case IASTUnaryExpression.op_star:
                Expression idx = o.expr;
                // Expression access = new ArrayAccessExpression(loc,
                // new IdentifierExpression(loc, SFO.MEMORY),
                // new Expression[] { idx });
                if (!(idx instanceof IdentifierExpression)) {
                    String msg = "Pointers on non primitive types not yet supported!";
                    Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax,
                            msg);
                    throw new UnsupportedSyntaxException(msg);
                }
                String cId = symbolTable.getCID4BoogieID(
                        ((IdentifierExpression) idx).getIdentifier(), loc);
                CType cvar = symbolTable.get(cId, loc).getCVariable();
                if (!(cvar instanceof CPointer)) {
                    String msg = "Type error!";
                    Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax,
                            msg);
                    throw new UnsupportedSyntaxException(msg);
                }
                cvar = ((CPointer) cvar).pointsToType;
                if (!(cvar instanceof CPrimitive)) {
                    String msg = "Pointers on non primitive types not yet supported!";
                    Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax,
                            msg);
                    throw new UnsupportedSyntaxException(msg);
                }
                InferredType t = tInt;
                switch ((((CPrimitive) cvar)).getType()) {
                    case BOOL:
                        t = tBool;
                        break;
                    case FLOAT:
                        t = new InferredType(Type.Real);
                        break;
                    case POINTER:
                        t = new InferredType(Type.Pointer);
                        break;
                    default:
                }
                ResultExpression a = memoryHandler.getReadCall(main, t, idx);
                Expression access = a.expr;
                o.stmt.addAll(a.stmt);
                o.decl.addAll(a.decl);
                o.auxVars.putAll(a.auxVars);
                // TODO : I think this is redundant!
            	// Matthias agreed and commented out
                /*
                if (idx.getType() instanceof InferredType
                        && ((InferredType) idx.getType()).getType() == Type.Pointer) {
                    o.stmt.add(memoryHandler.checkValidityOfAccess(idx));
                }
                */
                ResultExpression rex = new ResultExpression(o.stmt, access,
                        o.decl, o.auxVars);
                return rex;
            case IASTUnaryExpression.op_amper:
                decl = new ArrayList<Declaration>();
                stmt = new ArrayList<Statement>();
                auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
                // TODO : type not always Pointer!?
                t = new InferredType(Type.Pointer);
                ResultExpression read = memoryHandler.getReadCall(main, t,
                        o.expr);
                stmt.addAll(o.stmt);
                decl.addAll(o.decl);
                auxVars.putAll(o.auxVars);
                stmt.addAll(read.stmt);
                decl.addAll(read.decl);
                auxVars.putAll(read.auxVars);
                return new ResultExpression(stmt, read.expr, decl, auxVars);
            case IASTUnaryExpression.op_alignOf:
            case IASTUnaryExpression.op_tilde:
            default:
                String msg = "Unknown or unsupported unary operation: "
                        + node.getOperator();
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
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
        decl.addAll(l.decl);
        decl.addAll(r.decl);
        auxVars.putAll(l.auxVars);
        auxVars.putAll(r.auxVars);
        assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";

        if (l.expr instanceof IdentifierExpression
                || l.expr instanceof ArrayAccessExpression
                || l.expr instanceof StructAccessExpression) {
            if (r.expr instanceof IntegerLiteral && l.expr.getType() != null) {
                r.expr = main.typeHandler.convertArith2Boolean(loc,
                        new PrimitiveType(loc, l.expr.getType(), l.expr
                                .getType().toString()), r.expr);
            }
        }
        InferredType tBool = new InferredType(InferredType.Type.Boolean);
        InferredType tInt = new InferredType(InferredType.Type.Integer);

        switch (node.getOperator()) {
            case IASTBinaryExpression.op_assign:
                stmt.addAll(r.stmt);
                if (node.getOperand1() instanceof IASTUnaryExpression
                        && ((IASTUnaryExpression) node.getOperand1())
                                .getOperator() == IASTUnaryExpression.op_star) {
                    ResultExpression o = (ResultExpression) main
                            .dispatch(((IASTUnaryExpression) node.getOperand1())
                                    .getOperand());
                    stmt.addAll(o.stmt);
                    decl.addAll(o.decl);
                    auxVars.putAll(o.auxVars);
                    ResultExpression rex = memoryHandler.getWriteCall(o.expr,
                            r.expr);
                    stmt.addAll(rex.stmt);
                    decl.addAll(rex.decl);
                    auxVars.putAll(rex.auxVars);
                    for (String t : new String[] { SFO.INT, SFO.POINTER,
                            SFO.REAL, SFO.BOOL }) {
                        functionHandler.getModifiedGlobals()
                                .get(functionHandler.getCurrentProcedureID())
                                .add(SFO.MEMORY + "_" + t);
                    }
                    assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                    return new ResultExpression(stmt, rex.expr, decl, auxVars);
                } else if (l.expr.getType() instanceof InferredType
                        && ((InferredType) l.expr.getType()).getType() == Type.Pointer
                        && r.expr.getType() instanceof InferredType
                        && ((InferredType) r.expr.getType()).getType() != Type.Pointer) {
                    // This is considered insecure on most platforms. It will
                    // most probably lead to a seg. fault.
                    // String msg = "Using integer value as pointer!";
                    // Dispatcher.warn(loc, SyntaxErrorType.TypeError, msg);
                    // FIXME: Assign constant pointer t={0, r.expr }.
                    String tmpId = main.nameHandler
                            .getTempVarUID(SFO.AUXVAR.CONSTPOINTER);
                    InferredType tmpIType = new InferredType(Type.Pointer);
                    Expression idEx = new IdentifierExpression(loc,
                            new InferredType(Type.Pointer), tmpId);
                    VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpId, tmpIType, loc);
                    auxVars.put(tmpVar, loc);
                    decl.add(tmpVar);
                    stmt.add(new AssignmentStatement(
                            loc,
                            new LeftHandSide[] { new StructLHS(loc,
                                    new VariableLHS(loc, tmpId), SFO.POINTER_BASE) },
                            new Expression[] { new IntegerLiteral(loc, SFO.NR0) }));
                    stmt.add(new AssignmentStatement(loc,
                            new LeftHandSide[] { new StructLHS(loc,
                                    new VariableLHS(loc, tmpId),
                                    SFO.POINTER_OFFSET) },
                            new Expression[] { r.expr }));
                    r.expr = idEx;
                }
                stmt.addAll(l.stmt);
                LeftHandSide lhs = BoogieASTUtil.getLHSforExpression(l.expr);
                AssignmentStatement aStmt = new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs }, new Expression[] { r.expr });
                stmt.add(aStmt);
                functionHandler.checkIfModifiedGlobal(main,
                        BoogieASTUtil.getLHSId(lhs), loc);
                return new ResultExpression(stmt, l.expr, decl, auxVars);
            case IASTBinaryExpression.op_equals:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                return new ResultExpression(stmt, wrapBinaryBoolean2Int(loc,
                        BinaryExpression.Operator.COMPEQ, l.expr,
                        r.expr), decl, auxVars);
            case IASTBinaryExpression.op_greaterEqual:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                return new ResultExpression(stmt, wrapBinaryBoolean2Int(loc,
                		BinaryExpression.Operator.COMPGEQ, l.expr,
                        r.expr), decl, auxVars);
            case IASTBinaryExpression.op_greaterThan:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                return new ResultExpression(stmt, wrapBinaryBoolean2Int(loc,
                		BinaryExpression.Operator.COMPGT, l.expr,
                        r.expr), decl, auxVars);
            case IASTBinaryExpression.op_lessEqual:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                return new ResultExpression(stmt,  wrapBinaryBoolean2Int(loc,
                		BinaryExpression.Operator.COMPLEQ, l.expr,
                        r.expr), decl, auxVars);
            case IASTBinaryExpression.op_lessThan:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                return new ResultExpression(stmt, wrapBinaryBoolean2Int(loc,
                		BinaryExpression.Operator.COMPLT, l.expr,
                        r.expr), decl, auxVars);
            case IASTBinaryExpression.op_logicalAnd:
                stmt.addAll(l.stmt);
                if (r.auxVars.isEmpty() && l.auxVars.isEmpty()) {
                	// no auxVar in operands, hence no side effects in operands
                	// we can directly combine operands with LOGICAND
                	return new ResultExpression(stmt, wrapBinaryBoolean2Int(loc,
                    		BinaryExpression.Operator.LOGICAND,
                    		main.typeHandler.convertArith2Boolean(
                    				loc, new PrimitiveType(loc, SFO.BOOL),
                    				l.expr),
                            main.typeHandler.convertArith2Boolean(
                            		loc, new PrimitiveType(loc, SFO.BOOL),
                            		r.expr)),
                            decl, auxVars);
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
                // #t~AND~UID = false
                lhs = new VariableLHS(loc, tInt, resName);
                Expression[] rhs = new Expression[] { new IntegerLiteral(loc,
                        tInt, "0") };
                AssignmentStatement aStat = new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs }, rhs);
                stmt.add(aStat);
                // if (left) {#t~AND~UID = right;}
                // if (#t~AND~UID) { ... }
                ArrayList<Statement> outerThenPart = new ArrayList<Statement>();
                outerThenPart.addAll(r.stmt);
                outerThenPart
                        .add(new AssignmentStatement(loc,
                                new LeftHandSide[] { lhs },
                                new Expression[] { r.expr }));
                r.expr = main.typeHandler.convertArith2Boolean(loc,
                        new PrimitiveType(loc, SFO.BOOL), r.expr);
                l.expr = main.typeHandler.convertArith2Boolean(loc,
                        new PrimitiveType(loc, SFO.BOOL), l.expr);
                IfStatement ifStatement = new IfStatement(loc, l.expr,
                        outerThenPart.toArray(new Statement[0]),
                        new Statement[0]);
                stmt.add(ifStatement);
                return new ResultExpression(stmt, new IdentifierExpression(loc,
                        tBool, resName), decl, auxVars);
            case IASTBinaryExpression.op_logicalOr:
                stmt.addAll(l.stmt);
                if (r.auxVars.isEmpty() && l.auxVars.isEmpty()) {
                	// no auxVar in operands, hence no side effects in operands
                	// we can directly combine operands with LOGICOR
                	return new ResultExpression(stmt, wrapBinaryBoolean2Int(loc,
                    		BinaryExpression.Operator.LOGICOR,
                    		main.typeHandler.convertArith2Boolean(
                    				loc, new PrimitiveType(loc, SFO.BOOL),
                    				l.expr),
                            main.typeHandler.convertArith2Boolean(
                            		loc, new PrimitiveType(loc, SFO.BOOL),
                            		r.expr)),
                            decl, auxVars);
                }
                // create and add tmp var #t~OR~UID
                resName = main.nameHandler
                        .getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT);
                tempVar = new VarList(loc, new String[] { resName },
                        new PrimitiveType(loc, SFO.INT));
                tmpVar = new VariableDeclaration(loc, new Attribute[0],
                        new VarList[] { tempVar });
                auxVars.put(tmpVar, loc);
                decl.add(tmpVar);
                // #t~OR~UID = false
                lhs = new VariableLHS(loc, tInt, tempVar.getIdentifiers()[0]);
                // if (left) {#t~OR~UID = true;} else {#t~OR~UID = right}}
                // if (#t~OR~UID) { ... }
                Statement[] thenPart = new Statement[] { new AssignmentStatement(
                        loc,
                        new LeftHandSide[] { lhs },
                        new Expression[] { new IntegerLiteral(loc, tInt, "1") }) };
                ArrayList<Statement> elsePart = new ArrayList<Statement>();
                elsePart.addAll(r.stmt);
                elsePart.add(new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs }, new Expression[] { r.expr }));
                r.expr = main.typeHandler.convertArith2Boolean(loc,
                        new PrimitiveType(loc, SFO.BOOL), r.expr);
                l.expr = main.typeHandler.convertArith2Boolean(loc,
                        new PrimitiveType(loc, SFO.BOOL),l.expr);
                ifStatement = new IfStatement(loc, l.expr, thenPart,
                        elsePart.toArray(new Statement[0]));
                stmt.add(ifStatement);
                assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                return new ResultExpression(stmt, new IdentifierExpression(loc,
                        tBool, resName), decl, auxVars);
            case IASTBinaryExpression.op_notequals:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                return new ResultExpression(stmt, wrapBinaryBoolean2Int(loc,
                		BinaryExpression.Operator.COMPNEQ, l.expr,
                		r.expr), decl, auxVars);
            case IASTBinaryExpression.op_minus:
            case IASTBinaryExpression.op_plus:
            case IASTBinaryExpression.op_modulo:
            case IASTBinaryExpression.op_multiply:
            case IASTBinaryExpression.op_divide:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                if (node.getOperator() == IASTBinaryExpression.op_divide) {
                    CACSLLocation assertLoc = new CACSLLocation(node,
                            new Check(Check.Spec.DIVISION_BY_ZERO));
                    stmt.add(new AssertStatement(assertLoc,
                            new BinaryExpression(assertLoc,
                                    BinaryExpression.Operator.COMPNEQ,
                                    new IntegerLiteral(assertLoc, SFO.NR0),
                                    r.expr)));
                }
                Expression expr = createArithmeticExpression(
                        node.getOperator(), l.expr, r.expr, loc);
                assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                return new ResultExpression(stmt, expr, decl, auxVars);
            case IASTBinaryExpression.op_minusAssign:
            case IASTBinaryExpression.op_multiplyAssign:
            case IASTBinaryExpression.op_divideAssign:
            case IASTBinaryExpression.op_moduloAssign:
            case IASTBinaryExpression.op_plusAssign:
                // TODO : what to do with pointers? I think this should only
                // manipulate the pointers' offsets!
                stmt.addAll(r.stmt);
                stmt.addAll(l.stmt);
                if (node.getOperator() == IASTBinaryExpression.op_divideAssign) {
                    CACSLLocation assertLoc = new CACSLLocation(node,
                            new Check(Check.Spec.DIVISION_BY_ZERO));
                    stmt.add(new AssertStatement(assertLoc,
                            new BinaryExpression(assertLoc,
                                    BinaryExpression.Operator.COMPNEQ,
                                    new IntegerLiteral(assertLoc, SFO.NR0),
                                    r.expr)));
                }
                Expression be = createArithmeticExpression(node.getOperator(),
                        l.expr, r.expr, loc);
                if (node.getOperand1() instanceof IASTUnaryExpression
                        && ((IASTUnaryExpression) node.getOperand1())
                                .getOperator() == IASTUnaryExpression.op_star) {
                    ResultExpression o = (ResultExpression) main
                            .dispatch(((IASTUnaryExpression) node.getOperand1())
                                    .getOperand());
                    stmt.addAll(o.stmt);
                    decl.addAll(o.decl);
                    auxVars.putAll(o.auxVars);
                    ResultExpression rex = memoryHandler.getWriteCall(o.expr,
                            be);
                    stmt.addAll(rex.stmt);
                    decl.addAll(rex.decl);
                    auxVars.putAll(rex.auxVars);
                    for (String t : new String[] { SFO.INT, SFO.POINTER,
                            SFO.REAL, SFO.BOOL }) {
                        functionHandler.getModifiedGlobals()
                                .get(functionHandler.getCurrentProcedureID())
                                .add(SFO.MEMORY + "_" + t);
                    }
                    assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                    return new ResultExpression(stmt, rex.expr, decl, auxVars);
                }
                lhs = BoogieASTUtil.getLHSforExpression(l.expr);
                stmt.add(new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs }, new Expression[] { be }));
                functionHandler.checkIfModifiedGlobal(main,
                        BoogieASTUtil.getLHSId(lhs), loc);
                assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                return new ResultExpression(stmt, null, decl, auxVars);
            case IASTBinaryExpression.op_binaryAnd:
            case IASTBinaryExpression.op_binaryOr:
            case IASTBinaryExpression.op_binaryXor:
            case IASTBinaryExpression.op_shiftLeft:
            case IASTBinaryExpression.op_shiftRight:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                Expression bwexpr = createBitwiseExpression(node.getOperator(),
                        l.expr, r.expr, loc);
                assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                return new ResultExpression(stmt, bwexpr, decl, auxVars);
            case IASTBinaryExpression.op_shiftLeftAssign:
            case IASTBinaryExpression.op_shiftRightAssign:
                // return main.sideEffectHandler.visit(main, node);
            case IASTBinaryExpression.op_binaryAndAssign:
            case IASTBinaryExpression.op_binaryOrAssign:
            case IASTBinaryExpression.op_binaryXorAssign:
                stmt.addAll(l.stmt);
                stmt.addAll(r.stmt);
                Expression bwaexpr = createBitwiseExpression(
                        node.getOperator(), l.expr, r.expr, loc);
                if (node.getOperand1() instanceof IASTUnaryExpression
                        && ((IASTUnaryExpression) node.getOperand1())
                                .getOperator() == IASTUnaryExpression.op_star) {
                    ResultExpression o = (ResultExpression) main
                            .dispatch(((IASTUnaryExpression) node.getOperand1())
                                    .getOperand());
                    stmt.addAll(o.stmt);
                    decl.addAll(o.decl);
                    auxVars.putAll(o.auxVars);
                    ResultExpression rex = memoryHandler.getWriteCall(o.expr,
                            bwaexpr);
                    stmt.addAll(rex.stmt);
                    decl.addAll(rex.decl);
                    auxVars.putAll(rex.auxVars);
                    for (String t : new String[] { SFO.INT, SFO.POINTER,
                            SFO.REAL, SFO.BOOL }) {
                        functionHandler.getModifiedGlobals()
                                .get(functionHandler.getCurrentProcedureID())
                                .add(SFO.MEMORY + "_" + t);
                    }
                    assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                    return new ResultExpression(stmt, rex.expr, decl, auxVars);
                }
                lhs = BoogieASTUtil.getLHSforExpression(l.expr);
                stmt.add(new AssignmentStatement(loc,
                        new LeftHandSide[] { lhs },
                        new Expression[] { bwaexpr }));
                functionHandler.checkIfModifiedGlobal(main,
                        BoogieASTUtil.getLHSId(lhs), loc);
                assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
                return new ResultExpression(stmt, null, decl, auxVars);
            default:
                String msg = "Unknown or unsupported unary operation";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
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
     * @return the resulting binary expression
     */
    private static Expression createArithmeticExpression(int op,
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
        return functionHandler.handleReturnStatement(main, node);
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
                stmt.addAll(Dispatcher.createHavocsForAuxVars(rExp.auxVars));
                Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                        0);
                return new ResultExpression(stmt, null, decl, emptyAuxVars);
            } else if (res.expr != null) {
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
        Expression cond = condResult.expr;
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
                condResult = new ResultExpression(new BooleanLiteral(loc,
                        new InferredType(Type.Boolean), true),
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

        decl.addAll(condResult.decl);
        condResult.expr = main.typeHandler.convertArith2Boolean(loc,
                new PrimitiveType(loc, SFO.BOOL), condResult.expr);
        IfStatement ifStmt;
        {
            Expression cond = new UnaryExpression(loc,
                    UnaryExpression.Operator.LOGICNEG, condResult.expr);
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
                    "You might have parsed your code with ITranslationUnit.AST_SKIP_TRIVIAL_EXPRESSIONS_IN_AGGREGATE_INITIALIZERS!");
        }
        ResultExpressionListRec result = new ResultExpressionListRec();
        for (IASTInitializerClause i : node.getClauses()) {
            Result r = main.dispatch(i);
            if (r instanceof ResultExpressionListRec) {
                result.list.add((ResultExpressionListRec) r);
            } else if (r instanceof ResultExpression) {
                ResultExpression rex = (ResultExpression) r;
                result.list.add(new ResultExpressionListRec(rex.stmt, rex.expr,
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
        return structHandler.handleDesignatedInitializer(main, node);
    }

    @Override
    public Result visit(Dispatcher main, IASTFunctionCallExpression node) {
        return functionHandler.handleFunctionCallExpression(main,
                memoryHandler, node);
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
        ResultExpression l = (ResultExpression) switchParam;
        stmt.addAll(l.stmt);
        decl.addAll(l.decl);
        auxVars.putAll(l.auxVars);
        Expression switchArg = l.expr;
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
                    if (cond == null) {
                        if (child instanceof IASTDefaultStatement)
                            cond = res.expr;
                        else if (child instanceof IASTCaseStatement)
                            cond = new BinaryExpression(locC, Operator.COMPEQ,
                                    switchArg, res.expr);
                    } else {
                        if (child instanceof IASTDefaultStatement)
                            cond = new BinaryExpression(locC, Operator.LOGICOR,
                                    cond, res.expr);
                        else if (child instanceof IASTCaseStatement)
                            cond = new BinaryExpression(locC, Operator.LOGICOR,
                                    cond, new BinaryExpression(locC,
                                            Operator.COMPEQ, switchArg,
                                            res.expr));
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
        return new ResultExpression(c.stmt, c.expr, c.decl, c.auxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTDefaultStatement node) {
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
                0);
        return new ResultExpression(stmt, new BooleanLiteral(new CACSLLocation(
                node), new InferredType(Type.Boolean), true), decl,
                emptyAuxVars);
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
            return new ResultExpression(stmt, res.expr, decl, emptyAuxVars);
        } else if (r instanceof ResultSkip) {
            return new ResultExpression(stmt, null, decl, emptyAuxVars);
        } else { // r instanceof Result ...
            Expression expr = null;
            if (r.node instanceof Statement) {
                stmt.add((Statement) r.node);
            } else if (r.node instanceof Declaration) {
                decl.add((Declaration) r.node);
            } else if (r.node instanceof Expression) {
                expr = (Expression) r.node;
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
            return new ResultExpression(stmt, res.expr, decl, emptyAuxVars);
        } else if (r instanceof ResultSkip) {
            return new ResultExpression(stmt, null, decl, emptyAuxVars);
        } else { // r instanceof Result ...
            Expression expr = null;
            if (r.node instanceof Statement) {
                stmt.add((Statement) r.node);
            } else if (r.node instanceof Declaration) {
                decl.add((Declaration) r.node);
            } else if (r.node instanceof Expression) {
                expr = (Expression) r.node;
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
        
        Result rPositive = main.dispatch(node.getPositiveResultExpression());
        assert rPositive instanceof ResultExpression;
        ResultExpression rePositive = (ResultExpression) rPositive;
        
        Result rNegative = main.dispatch(node.getNegativeResultExpression());
        assert rNegative instanceof ResultExpression;
        ResultExpression reNegative = (ResultExpression) rNegative;
        
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        Map<VariableDeclaration, CACSLLocation> auxVars = 
        		new HashMap<VariableDeclaration, CACSLLocation>(0);
        decl.addAll(reLocCond.decl);
        stmt.addAll(reLocCond.stmt);
        String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.ITE);
        InferredType tmpIType = (InferredType) rePositive.expr.getType();
        assert (tmpIType.equals(reNegative.expr.getType()));
        VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
        decl.add(tmpVar);
        Expression condition = reLocCond.expr;
        condition = main.typeHandler.convertArith2Boolean(loc, new PrimitiveType(
                loc, SFO.BOOL), condition);
        List<Statement> ifStatements = new ArrayList<Statement>();
        {
        	ifStatements.addAll(rePositive.stmt);
        	LeftHandSide[] lhs = { new VariableLHS(loc, tmpName) };
        	AssignmentStatement assign = new AssignmentStatement(loc, lhs, new Expression[] { rePositive.expr });
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
        	AssignmentStatement assign = new AssignmentStatement(loc, lhs, new Expression[] { reNegative.expr });
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
        return new ResultExpression(stmt, tmpExpr, decl, auxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTArraySubscriptExpression node) {
        return arrayHandler.handleArraySubscriptionExpression(main, node);
    }

    @Override
    public Result visit(Dispatcher main, IASTInitializerClause node) {
        assert node.getChildren().length == 1;
        Result r = main.dispatch(node.getChildren()[0]);
        assert r instanceof ResultExpression;
        ResultExpression rex = (ResultExpression) r;
        return new ResultExpression(rex.expr, rex.auxVars);
    }

    @Override
    public Result visit(Dispatcher main, IASTFieldReference node) {
        return structHandler.handleFieldReference(main, node);
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
                return new ResultExpression(memoryHandler.getSizeOf(main, node
                        .getTypeId().getDeclSpecifier()), emptyAuxVars);
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
