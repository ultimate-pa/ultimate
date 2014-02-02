/**
 * An example for a main dispatcher implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.text.ParseException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTContinueStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationListOwner;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTFunctionStyleMacroParameter;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTImplicitName;
import org.eclipse.cdt.core.dom.ast.IASTImplicitNameOwner;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorErrorStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorObjectStyleMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorPragmaStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorUndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblem;
import org.eclipse.cdt.core.dom.ast.IASTProblemDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTProblemExpression;
import org.eclipse.cdt.core.dom.ast.IASTProblemStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblemTypeId;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdInitializerExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.IArrayType;
import org.eclipse.cdt.core.dom.ast.IBasicType;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.internal.core.dom.parser.IASTAmbiguousExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.cpp.IASTAmbiguousCondition;

import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLType;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assertion;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assumes;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.AtLabelExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Axiomatic;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BaseAddrExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Behavior;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BlockLengthExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Case;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeForBehavior;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Completeness;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ContractStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Decreases;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FreeableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Inductive;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Invariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Lemma;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LogicFunction;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LogicStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAssigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopForBehavior;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopVariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.MallocableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ModelVariable;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.NotDefinedExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.NullPointer;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Parameter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.PolyIdentifier;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Predicate;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.SizeOfExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.SyntacticNamingExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Terminates;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.TypeInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Backtranslator;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
public class MainDispatcher extends Dispatcher {
    /**
     * The current decorator tree.
     */
    private DecoratorNode decoratorTree;
    /**
     * The iterator for the current decorator tree.
     */
    private Iterator<DecoratorNode> decoratorTreeIterator;
    /**
     * Temp variable for next ACSL calculation.
     */
    private DecoratorNode nextACSLBuffer;
    /**
     * Whether the memory model is required.
     */
    private boolean isMMRequired;
    /**
     * Variables that need some special memory handling.
     */
    private HashSet<IASTNode> variablesOnHeap;
    /**
     * Functions used as pointer.
     */
    private HashMap<String, IASTFunctionDefinition> functionsOnHeap;
    
    /**
     * @return a map of functions used as pointers.
     * @author Christian
     */
    public HashMap<String, IASTFunctionDefinition> getFunctionPointers() {
        return functionsOnHeap;
    }
    
    //begin alex
    private HashSet<VariableDeclaration> _boogieDeclarationsOfVariablesOnHeap;

    void addBoogieDeclarationOfVariableOnHeap(VariableDeclaration vd) {
    	if (_boogieDeclarationsOfVariablesOnHeap == null)
    		_boogieDeclarationsOfVariablesOnHeap = new HashSet<VariableDeclaration>();
    	_boogieDeclarationsOfVariablesOnHeap.add(vd);
    }
    
    boolean getBoogieDeclarationsOfVariablesOnHeapContains(VariableDeclaration vd) {
    	if (_boogieDeclarationsOfVariablesOnHeap == null)
    		return false;
    	return _boogieDeclarationsOfVariablesOnHeap.contains(vd);
    }
    
    //end alex

    public MainDispatcher(Backtranslator backtranslator) {
		super(backtranslator);
	}

	@Override
    public boolean isMMRequired() {
        return isMMRequired;
    }

    /**
     * Returns a set of variables, that have to be handled using the memory
     * model.
     * 
     * @return a set of variables, that have to be handled using the memory
     *         model.
     */
    public HashSet<IASTNode> getVariablesForHeap() {
        return variablesOnHeap;
    }

    @Override
    protected void preRun(DecoratorNode node) {
        assert node.getCNode() != null;
        assert node.getCNode() instanceof IASTTranslationUnit;
        IASTTranslationUnit tu = (IASTTranslationUnit) node.getCNode();
        PreRunner pr = new PreRunner();
        tu.accept(pr);
        variablesOnHeap = pr.getVarsForHeap();
        functionsOnHeap = pr.getFunctionPointers();
        if (functionsOnHeap.size() > 0) {
            isMMRequired = true;
        }
        else {
            isMMRequired = pr.isMMRequired();
        }
    }

    @Override
    protected void init() {
        sideEffectHandler = new SideEffectHandler();
        cHandler = new CHandler(this, backtranslator, true);
        typeHandler = new TypeHandler();
        acslHandler = new ACSLHandler();
        nameHandler = new NameHandler();
        backtranslator.setBoogie2C(nameHandler.getBoogie2C());
        preprocessorHandler = new PreprocessorHandler();
        REPORT_WARNINGS = true;
    }

    @Override
    public Result dispatch(IASTNode n) {
        if (n instanceof IASTTranslationUnit) {
            return cHandler.visit(this, ((IASTTranslationUnit) n));
        }
        if (n instanceof IASTSimpleDeclaration) {
            return cHandler.visit(this, (IASTSimpleDeclaration) n);
        }
        if (n instanceof IASTParameterDeclaration) {
            return cHandler.visit(this, (IASTParameterDeclaration) n);
        }
        if (n instanceof IASTDeclarator) {
            return cHandler.visit(this, (IASTDeclarator) n);
        }
        if (n instanceof IASTFunctionDefinition) {
            return cHandler.visit(this, (IASTFunctionDefinition) n);
        }
        if (n instanceof IASTArrayModifier) {
            return cHandler.visit(this, (IASTArrayModifier) n);
        }
        if (n instanceof IASTComment) {
            // TODO : remove? I think they are excluded by the parser anyway?
            return cHandler.visit(this, (IASTComment) n);
        }
        if (n instanceof IASTDeclaration) {
            return cHandler.visit(this, (IASTDeclaration) n);
        }
        if (n instanceof IASTDeclSpecifier) {
            // Here we decide which further Interface we want to visit, and
            // call the typeHandler
            if (n instanceof IASTSimpleDeclSpecifier) {
                return typeHandler.visit(this, (IASTSimpleDeclSpecifier) n);
            }
            if (n instanceof IASTNamedTypeSpecifier) {
                return typeHandler.visit(this, (IASTNamedTypeSpecifier) n);
            }
            if (n instanceof IASTEnumerationSpecifier) {
                return typeHandler.visit(this, (IASTEnumerationSpecifier) n);
            }
            if (n instanceof IASTElaboratedTypeSpecifier) {
                return typeHandler.visit(this, (IASTElaboratedTypeSpecifier) n);
            }
            if (n instanceof IASTCompositeTypeSpecifier) {
                return typeHandler.visit(this, (IASTCompositeTypeSpecifier) n);
            }
            return cHandler.visit(this, (IASTDeclSpecifier) n);
        }
        if (n instanceof IASTDeclarationListOwner) {
            // must be after IASTCompositeTypeSpecifier!
            return cHandler.visit(this, (IASTDeclarationListOwner) n);
        }
        if (n instanceof IASTStatement) {
            if (n instanceof IASTReturnStatement) {
                return cHandler.visit(this, (IASTReturnStatement) n);
            }
            if (n instanceof IASTSwitchStatement) {
                return cHandler.visit(this, (IASTSwitchStatement) n);
            }
            if (n instanceof IASTWhileStatement) {
                return cHandler.visit(this, (IASTWhileStatement) n);
            }
            if (n instanceof IASTLabelStatement) {
                return cHandler.visit(this, (IASTLabelStatement) n);
            }
            if (n instanceof IASTNullStatement) {
                return cHandler.visit(this, (IASTNullStatement) n);
            }
            if (n instanceof IASTContinueStatement) {
                return cHandler.visit(this, (IASTContinueStatement) n);
            }
            if (n instanceof IASTDeclarationStatement) {
                return cHandler.visit(this, (IASTDeclarationStatement) n);
            }
            if (n instanceof IASTDefaultStatement) {
                return cHandler.visit(this, (IASTDefaultStatement) n);
            }
            if (n instanceof IASTDoStatement) {
                return cHandler.visit(this, (IASTDoStatement) n);
            }
            if (n instanceof IASTExpressionStatement) {
                return cHandler.visit(this, (IASTExpressionStatement) n);
            }
            if (n instanceof IASTForStatement) {
                return cHandler.visit(this, (IASTForStatement) n);
            }
            if (n instanceof IASTGotoStatement) {
                return cHandler.visit(this, (IASTGotoStatement) n);
            }
            if (n instanceof IASTIfStatement) {
                return cHandler.visit(this, (IASTIfStatement) n);
            }
            if (n instanceof IASTCompoundStatement) {
                return cHandler.visit(this, (IASTCompoundStatement) n);
            }
            if (n instanceof IASTBreakStatement) {
                return cHandler.visit(this, (IASTBreakStatement) n);
            }
            if (n instanceof IASTCaseStatement) {
                return cHandler.visit(this, (IASTCaseStatement) n);
            }
            if (n instanceof IASTProblemStatement) {
                // error -> we will cancel the translation anyway ...
                // -> should be at the end of the parent if for performance
                return cHandler.visit(this, (IASTProblemStatement) n);
            }
            return cHandler.visit(this, (IASTStatement) n);
        }
        if (n instanceof IASTInitializer) {
            if (n instanceof IASTEqualsInitializer) {
                return cHandler.visit(this, (IASTEqualsInitializer) n);
            }
            if (n instanceof CASTDesignatedInitializer) {
                return cHandler.visit(this, (CASTDesignatedInitializer) n);
            }
            if (n instanceof IASTInitializerList) {
                return cHandler.visit(this, (IASTInitializerList) n);
            }
            return cHandler.visit(this, (IASTInitializer) n);
        }
        if (n instanceof IASTExpression) {
            if (n instanceof IASTLiteralExpression) {
                return cHandler.visit(this, (IASTLiteralExpression) n);
            }
            if (n instanceof IASTIdExpression) {
                return cHandler.visit(this, (IASTIdExpression) n);
            }
            if (n instanceof IASTFunctionCallExpression) {
                return cHandler.visit(this, (IASTFunctionCallExpression) n);
            }
            if (n instanceof IASTFieldReference) {
                return cHandler.visit(this, (IASTFieldReference) n);
            }
            if (n instanceof IASTExpressionList) {
                return cHandler.visit(this, (IASTExpressionList) n);
            }
            if (n instanceof IASTConditionalExpression) {
                return cHandler.visit(this, (IASTConditionalExpression) n);
            }
            if (n instanceof IASTCastExpression) {
                return cHandler.visit(this, (IASTCastExpression) n);
            }
            if (n instanceof IASTBinaryExpression) {
                return cHandler.visit(this, (IASTBinaryExpression) n);
            }
            if (n instanceof IASTBinaryTypeIdExpression) {
                return cHandler.visit(this, (IASTBinaryTypeIdExpression) n);
            }
            if (n instanceof IASTArraySubscriptExpression) {
                return cHandler.visit(this, (IASTArraySubscriptExpression) n);
            }
            if (n instanceof IASTAmbiguousExpression) {
                return cHandler.visit(this, (IASTAmbiguousExpression) n);
            }
            if (n instanceof IASTAmbiguousCondition) {
                return cHandler.visit(this, (IASTAmbiguousCondition) n);
            }
            if (n instanceof IASTTypeIdExpression) {
                return cHandler.visit(this, (IASTTypeIdExpression) n);
            }
            if (n instanceof IASTTypeIdInitializerExpression) {
                return cHandler
                        .visit(this, (IASTTypeIdInitializerExpression) n);
            }
            if (n instanceof IASTUnaryExpression) {
                return cHandler.visit(this, (IASTUnaryExpression) n);
            }
            if (n instanceof IASTProblemExpression) {
                return cHandler.visit(this, (IASTProblemExpression) n);
            }
            return cHandler.visit(this, (IASTExpression) n);
        }
        if (n instanceof IASTFunctionStyleMacroParameter) {
            return cHandler.visit(this, (IASTFunctionStyleMacroParameter) n);
        }
        if (n instanceof IASTImplicitNameOwner) {
            return cHandler.visit(this, (IASTImplicitNameOwner) n);
        }
        if (n instanceof IASTName) {
            return cHandler.visit(this, (IASTName) n);
        }
        if (n instanceof IASTPointerOperator) {
            return cHandler.visit(this, (IASTPointerOperator) n);
        }
        if (n instanceof IASTPreprocessorMacroExpansion) {
            return cHandler.visit(this, (IASTPreprocessorMacroExpansion) n);
        }
        if (n instanceof IASTProblem) {
            return cHandler.visit(this, (IASTProblem) n);
        }
        if (n instanceof IASTTypeId) {
            return cHandler.visit(this, (IASTTypeId) n);
        }
        // Indirect implementations of IASTNode in CDT version 7:
        if (n instanceof IASTArrayDeclarator) {
            return cHandler.visit(this, (IASTArrayDeclarator) n);
        }
        if (n instanceof IASTASMDeclaration) {
            return cHandler.visit(this, (IASTASMDeclaration) n);
        }
        if (n instanceof IASTCompositeTypeSpecifier) {
            return cHandler.visit(this, (IASTCompositeTypeSpecifier) n);
        }
        if (n instanceof IASTFieldDeclarator) {
            return cHandler.visit(this, (IASTFieldDeclarator) n);
        }
        if (n instanceof IASTImplicitName) {
            return cHandler.visit(this, (IASTImplicitName) n);
        }
        if (n instanceof IASTInitializerClause) {
            return cHandler.visit(this, (IASTInitializerClause) n);
        }
        if (n instanceof IASTPointer) {
            return cHandler.visit(this, (IASTPointer) n);
        }
        if (n instanceof IASTPreprocessorMacroDefinition) {
            return cHandler.visit(this, (IASTPreprocessorMacroDefinition) n);
        }
        if (n instanceof IASTPreprocessorObjectStyleMacroDefinition) {
            return cHandler.visit(this,
                    (IASTPreprocessorObjectStyleMacroDefinition) n);
        }
        if (n instanceof IASTStandardFunctionDeclarator) {
            return cHandler.visit(this, (IASTStandardFunctionDeclarator) n);
        }
        if (n instanceof IASTProblemDeclaration) {
            // error -> we will cancel the translation anyway ...
            // -> should be at the end of the parent if for performance
            return cHandler.visit(this, (IASTProblemDeclaration) n);
        }
        if (n instanceof IASTProblemTypeId) {
            // error -> we will cancel the translation anyway ...
            // -> should be at the end of the parent if for performance
            return cHandler.visit(this, (IASTProblemTypeId) n);
        }
        String msg = "MainDispatcher: AST node type unknown: " + n.getClass();
        ILocation loc = new CACSLLocation(n);
        Dispatcher.unsupportedSyntax(loc, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    @Override
    public Result dispatch(ACSLNode n) {
        if (n instanceof CodeAnnot) {
            return acslHandler.visit(this, (CodeAnnot) n);
        }
        if (n instanceof Expression) {
            if (n instanceof BinaryExpression) {
                return acslHandler.visit(this, (BinaryExpression) n);
            }
            if (n instanceof NotDefinedExpression) {
                return acslHandler.visit(this, (NotDefinedExpression) n);
            }
            if (n instanceof UnaryExpression) {
                return acslHandler.visit(this, (UnaryExpression) n);
            }
            if (n instanceof ArrayAccessExpression) {
                return acslHandler.visit(this, (ArrayAccessExpression) n);
            }
            if (n instanceof ArrayStoreExpression) {
                return acslHandler.visit(this, (ArrayStoreExpression) n);
            }
            if (n instanceof BitVectorAccessExpression) {
                return acslHandler.visit(this, (BitVectorAccessExpression) n);
            }
            if (n instanceof BooleanLiteral) {
                return acslHandler.visit(this, (BooleanLiteral) n);
            }
            if (n instanceof IntegerLiteral) {
                return acslHandler.visit(this, (IntegerLiteral) n);
            }
            if (n instanceof RealLiteral) {
                return acslHandler.visit(this, (RealLiteral) n);
            }
            if (n instanceof StringLiteral) {
                return acslHandler.visit(this, (StringLiteral) n);
            }
            if (n instanceof NullPointer) {
                return acslHandler.visit(this, (NullPointer) n);
            }
            if (n instanceof ValidExpression) {
                return acslHandler.visit(this, (ValidExpression) n);
            }
            if (n instanceof FreeableExpression) {
                return acslHandler.visit(this, (FreeableExpression) n);
            }
            if (n instanceof MallocableExpression) {
                return acslHandler.visit(this, (MallocableExpression) n);
            }
            if (n instanceof ResultExpression) {
                return acslHandler.visit(this, (ResultExpression) n);
            }
            if (n instanceof FieldAccessExpression) {
                return acslHandler.visit(this, (FieldAccessExpression) n);
            }
            if (n instanceof SizeOfExpression) {
                return acslHandler.visit(this, (SizeOfExpression) n);
            }
            if (n instanceof OldValueExpression) {
                return acslHandler.visit(this, (OldValueExpression) n);
            }
            if (n instanceof AtLabelExpression) {
                return acslHandler.visit(this, (AtLabelExpression) n);
            }
            if (n instanceof BaseAddrExpression) {
                return acslHandler.visit(this, (BaseAddrExpression) n);
            }
            if (n instanceof BlockLengthExpression) {
                return acslHandler.visit(this, (BlockLengthExpression) n);
            }
            if (n instanceof SyntacticNamingExpression) {
                return acslHandler.visit(this, (SyntacticNamingExpression) n);
            }
            if (n instanceof IdentifierExpression) {
                return acslHandler.visit(this, (IdentifierExpression) n);
            }
            if (n instanceof FunctionApplication) {
                return acslHandler.visit(this, (FunctionApplication) n);
            }
            if (n instanceof IfThenElseExpression) {
                return acslHandler.visit(this, (IfThenElseExpression) n);
            }
            if (n instanceof QuantifierExpression) {
                return acslHandler.visit(this, (QuantifierExpression) n);
            }
            if (n instanceof WildcardExpression) {
                return acslHandler.visit(this, (WildcardExpression) n);
            }
            return acslHandler.visit(this, (Expression) n);
        }
        if (n instanceof Contract) {
            return acslHandler.visit(this, (Contract) n);
        }
        if (n instanceof ContractStatement) {
            if (n instanceof Requires) {
                return acslHandler.visit(this, (Requires) n);
            }
            if (n instanceof Terminates) {
                return acslHandler.visit(this, (Terminates) n);
            }
            if (n instanceof Decreases) {
                return acslHandler.visit(this, (Decreases) n);
            }
            if (n instanceof Ensures) {
                return acslHandler.visit(this, (Ensures) n);
            }
            if (n instanceof Assigns) {
                return acslHandler.visit(this, (Assigns) n);
            }
            if (n instanceof Assumes) {
                return acslHandler.visit(this, (Assumes) n);
            }
            return acslHandler.visit(this, (ContractStatement) n);
        }
        if (n instanceof Completeness) {
            return acslHandler.visit(this, (Completeness) n);
        }
        if (n instanceof Behavior) {
            return acslHandler.visit(this, (Behavior) n);
        }
        if (n instanceof LogicStatement) {
            if (n instanceof Predicate) {
                return acslHandler.visit(this, (Predicate) n);
            }
            if (n instanceof LogicFunction) {
                return acslHandler.visit(this, (LogicFunction) n);
            }
            if (n instanceof Lemma) {
                return acslHandler.visit(this, (Lemma) n);
            }
            if (n instanceof Inductive) {
                return acslHandler.visit(this, (Inductive) n);
            }
            if (n instanceof Axiom) {
                return acslHandler.visit(this, (Axiom) n);
            }
            if (n instanceof Axiomatic) {
                return acslHandler.visit(this, (Axiomatic) n);
            }
            return acslHandler.visit(this, (LogicStatement) n);
        }
        if (n instanceof Invariant) {
            if (n instanceof GlobalInvariant) {
                return acslHandler.visit(this, (GlobalInvariant) n);
            }
            if (n instanceof TypeInvariant) {
                return acslHandler.visit(this, (TypeInvariant) n);
            }
            return acslHandler.visit(this, (Invariant) n);
        }
        if (n instanceof LoopStatement) {
            if (n instanceof LoopInvariant) {
                return acslHandler.visit(this, (LoopInvariant) n);
            }
            if (n instanceof LoopVariant) {
                return acslHandler.visit(this, (LoopVariant) n);
            }
            if (n instanceof LoopAssigns) {
                return acslHandler.visit(this, (LoopAssigns) n);
            }
            return acslHandler.visit(this, (LoopStatement) n);
        }
        if (n instanceof CodeStatement) {
            if (n instanceof Assertion) {
                return acslHandler.visit(this, (Assertion) n);
            }
            if (n instanceof CodeInvariant) {
                return acslHandler.visit(this, (CodeInvariant) n);
            }
            return acslHandler.visit(this, (CodeStatement) n);
        }
        if (n instanceof ACSLType) {
            return acslHandler.visit(this, (ACSLType) n);
        }
        if (n instanceof Case) {
            return acslHandler.visit(this, (Case) n);
        }
        if (n instanceof CodeForBehavior) {
            return acslHandler.visit(this, (CodeForBehavior) n);
        }
        if (n instanceof LoopAnnot) {
            return acslHandler.visit(this, (LoopAnnot) n);
        }
        if (n instanceof LoopForBehavior) {
            return acslHandler.visit(this, (LoopForBehavior) n);
        }
        if (n instanceof ModelVariable) {
            return acslHandler.visit(this, (ModelVariable) n);
        }
        if (n instanceof Parameter) {
            return acslHandler.visit(this, (Parameter) n);
        }
        if (n instanceof PolyIdentifier) {
            return acslHandler.visit(this, (PolyIdentifier) n);
        }
        if (n instanceof ACSLNode) {
            return acslHandler.visit(this, (ACSLNode) n);
        }
        String msg = "MainDispatcher: ACSL node type unknown: " + n.getClass();
        ILocation loc = new CACSLLocation(n);
        Dispatcher.unsupportedSyntax(loc, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    @Override
    public Result dispatch(DecoratorNode node) {
        this.decoratorTree = node;
        this.decoratorTreeIterator = node.iterator();
        if (node.getCNode() != null) {
            return dispatch(node.getCNode());
        }
        return dispatch(node.getAcslNode());
    }

    @Override
    public NextACSL nextACSLStatement() throws ParseException {
        DecoratorNode current;
        if (nextACSLBuffer != null) {
            current = nextACSLBuffer;
            nextACSLBuffer = null;
        } else {
            if (!decoratorTreeIterator.hasNext()) {
                return null;
            }
            current = decoratorTreeIterator.next();
        }
        while (decoratorTreeIterator.hasNext() && current.getAcslNode() == null) {
            // jump over C nodes.
            current = decoratorTreeIterator.next();
        }
        if (!decoratorTreeIterator.hasNext() && current.getCNode() != null) {
            return null;
        }
        // current = found ACSL node
        ArrayList<ACSLNode> acsl = new ArrayList<ACSLNode>();
        checkACSLLocation(current);
        acsl.add(current.getAcslNode());
        if (!decoratorTreeIterator.hasNext()) {
            // We found an ACSL node without a successor C node!
            if (current.getParent().getCNode() instanceof IASTTranslationUnit) {
                throw new IllegalArgumentException(
                        "ACSL on invalid location! line: "
                                + current.getAcslNode().getStartingLineNumber());
            }
            return new NextACSL(acsl, null);
        }
        // find successor C node with same parent as the found acsl node
        Iterator<DecoratorNode> myIterator = decoratorTree.iterator();
        DecoratorNode cNode = decoratorTree;
        while (myIterator.hasNext()
                && (cNode.getAcslNode() == null || !cNode.equals(current))) {
            cNode = myIterator.next();
        }
        // both iterators are on the same node --> cNode == current
        assert cNode.equals(current);
        while (myIterator.hasNext() && cNode.getAcslNode() != null) {
            cNode = myIterator.next();
        }
        IASTNode successor;
        if (cNode.getCNode() != null
                && cNode.getCNode().getParent()
                        .equals(current.getParent().getCNode())) {
            successor = cNode.getCNode();
        } else {
            successor = null;
        }

        DecoratorNode nextNode = decoratorTreeIterator.next();
        // block of ACSL nodes
        while (decoratorTreeIterator.hasNext() && nextNode.getCNode() == null) {
            // check parent of acsl nodes to be equivalent
            if (!current.getParent().getCNode()
                    .equals(nextNode.getParent().getCNode())) {
                // parent changed! not one block!
                assert nextACSLBuffer == null;
                if (nextNode.getAcslNode() != null) {
                    nextACSLBuffer = nextNode;
                }
                return new NextACSL(acsl, successor);
            }
            checkACSLLocation(nextNode);
            acsl.add(nextNode.getAcslNode());
            nextNode = decoratorTreeIterator.next();
        }
        if (nextNode.getAcslNode() != null
                && current.getParent().getCNode()
                        .equals(nextNode.getParent().getCNode())) {
            acsl.add(nextNode.getAcslNode());
        } else if (nextNode.getAcslNode() != null) {
            nextACSLBuffer = nextNode;
        }
        nextAcsl = new NextACSL(acsl, successor);
        return new NextACSL(acsl, successor);
    }

    /**
     * Parent node of an ACSL node should be a decorator node containing C. The
     * C node should be instance of IASTCompoundStatement or
     * IASTTranslationUnit.<br>
     * <b>ACSL is unexpected in other locations.</b>
     * 
     * @param acslNode
     *            the ACSL holding decorator node that should be checked.
     */
    private static void checkACSLLocation(DecoratorNode acslNode) {
        if (acslNode.getAcslNode() == null) {
            throw new IllegalArgumentException(
                    "The given decorator node is not holding ACSL"
                            + acslNode.getCNode().getRawSignature());
        }
        if (acslNode.getParent().getCNode() == null) {
            throw new IllegalArgumentException(
                    "The parent node of the given ACSL holding decorator node is not a C node!");
        }
        if (!(acslNode.getParent().getCNode() instanceof IASTTranslationUnit)
                && !(acslNode.getParent().getCNode() instanceof IASTCompoundStatement)) {
            throw new IllegalArgumentException(
                    "The location of the given ACSL holding decorator node is unexpected!");
        }
    }

    @Override
    public InferredType dispatch(IType type) {
        // All Known Subinterfaces:
        // IArrayType, IBasicType, ICArrayType, ICBasicType, ICompositeType,
        // ICPointerType, ICPPBasicType, ICPPClassSpecialization,
        // ICPPClassTemplate, ICPPClassTemplatePartialSpecialization,
        // ICPPClassTemplatePartialSpecializationSpecialization, ICPPClassType,
        // ICPPEnumeration, ICPPFunctionType, ICPPParameterPackType,
        // ICPPPointerToMemberType, ICPPReferenceType,
        // ICPPTemplateTemplateParameter, ICPPTemplateTypeParameter,
        // ICQualifierType, IEnumeration, IFunctionType, IGPPBasicType,
        // IGPPPointerToMemberType, IGPPPointerType, IGPPQualifierType,
        // IPointerType, IProblemBinding, IProblemType, IQualifierType, ITypedef
        if (type instanceof IBasicType) {
            return typeHandler.visit(this, (IBasicType) type);
        }
        if (type instanceof ITypedef) {
            return typeHandler.visit(this, (ITypedef) type);
        }
        if (type instanceof IArrayType) {
            return typeHandler.visit(this, (IArrayType) type);
        }
        return typeHandler.visit(this, type);
    }

    @Override
    public Result dispatch(IASTPreprocessorStatement n) {
        if (n instanceof IASTPreprocessorElifStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorElifStatement) n);
        }
        if (n instanceof IASTPreprocessorElseStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorElseStatement) n);
        }
        if (n instanceof IASTPreprocessorEndifStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorEndifStatement) n);
        }
        if (n instanceof IASTPreprocessorErrorStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorErrorStatement) n);
        }
        if (n instanceof IASTPreprocessorIfdefStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorIfdefStatement) n);
        }
        if (n instanceof IASTPreprocessorIfndefStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorIfndefStatement) n);
        }
        if (n instanceof IASTPreprocessorIfStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorIfStatement) n);
        }
        if (n instanceof IASTPreprocessorIncludeStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorIncludeStatement) n);
        }
        if (n instanceof IASTPreprocessorMacroDefinition) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorMacroDefinition) n);
        }
        if (n instanceof IASTPreprocessorPragmaStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorPragmaStatement) n);
        }
        if (n instanceof IASTPreprocessorUndefStatement) {
            return preprocessorHandler.visit(this,
                    (IASTPreprocessorUndefStatement) n);
        }
        return preprocessorHandler.visit(this, n);
    }
}
