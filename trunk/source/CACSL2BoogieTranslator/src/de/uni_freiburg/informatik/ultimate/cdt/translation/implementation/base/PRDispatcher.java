package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.text.ParseException;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import org.apache.log4j.Logger;
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
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorObjectStyleMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.SvComp14PRCHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler.SVCompTypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;

public class PRDispatcher extends Dispatcher {
	
	LinkedHashSet<IASTDeclaration> reachableDeclarations;

	public PRDispatcher(CACSL2BoogieBacktranslator backtranslator,
			IUltimateServiceProvider services, Logger logger, LinkedHashMap<String,Integer> functionToIndex, LinkedHashSet<IASTDeclaration> reachableDeclarations) {
		super(backtranslator, services, logger);
		mFunctionToIndex = functionToIndex;
		this.reachableDeclarations = reachableDeclarations;
	}

	@Override
	protected void init() {

		nameHandler = new NameHandler(backtranslator);
		typeHandler = new SVCompTypeHandler();
		cHandler = new SvComp14PRCHandler(this, backtranslator, false, mLogger, typeHandler);
	}

	@Override
	public Result dispatch(DecoratorNode node) {
//		this.decoratorTree = node;
//		this.decoratorTreeIterator = node.iterator();
		if (node.getCNode() != null) {
			return dispatch(node.getCNode());
		}
		return dispatch(node.getAcslNode());
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
		if (n instanceof IASTASMDeclaration) {
			return cHandler.visit(this, (IASTASMDeclaration) n);
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
				return cHandler.visit(this, (IASTTypeIdInitializerExpression) n);
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
			return cHandler.visit(this, (IASTPreprocessorObjectStyleMacroDefinition) n);
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
		ILocation loc = LocationFactory.createCLocation(n);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result dispatch(IASTPreprocessorStatement node) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public InferredType dispatch(IType type) {
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
	public Result dispatch(ACSLNode node) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected void preRun(DecoratorNode node) {
		// TODO Auto-generated method stub

	}

	@Override
	public NextACSL nextACSLStatement() throws ParseException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isMMRequired() {
		// TODO Auto-generated method stub
		return false;
	}
	LinkedHashSet<IASTDeclaration> getReachableDeclarationsOrDeclarators() {
		return reachableDeclarations;
	}
}
