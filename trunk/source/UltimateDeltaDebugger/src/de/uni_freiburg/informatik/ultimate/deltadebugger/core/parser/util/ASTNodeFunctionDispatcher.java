/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.Optional;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTAlignmentSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTAttribute;
import org.eclipse.cdt.core.dom.ast.IASTAttributeSpecifier;
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
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier.IASTEnumerator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTImplicitDestructorName;
import org.eclipse.cdt.core.dom.ast.IASTImplicitName;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
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
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorFunctionStyleMacroDefinition;
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
import org.eclipse.cdt.core.dom.ast.IASTToken;
import org.eclipse.cdt.core.dom.ast.IASTTokenList;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdInitializerExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.c.ICASTArrayDesignator;
import org.eclipse.cdt.core.dom.ast.c.ICASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignatedInitializer;
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignator;
import org.eclipse.cdt.core.dom.ast.c.ICASTFieldDesignator;
import org.eclipse.cdt.core.dom.ast.c.ICASTPointer;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTCapture;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTClassVirtSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTCompositeTypeSpecifier.ICPPASTBaseSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTDecltypeSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTNamespaceDefinition;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTemplateParameter;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTVirtSpecifier;
import org.eclipse.cdt.core.dom.ast.gnu.IGCCASTAttributeSpecifier;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.gnu.c.IGCCASTArrayRangeDesignator;

/**
 * Contains the instanceof mess that is necessary to detect the actual runtime type of an IASTNode and call the correct
 * overload of an IASTNodeFunction object.
 * Note: The idea of this class is to move the complexity out of the rest of the code, that needs to detect the runtime
 * type of an IASTNode.
 * <p>
 * The Cyclomatic Complexity (and other complexity metrics) cannot be reduced without artificially obfuscating the code.
 * 
 * @param <T>
 *            function return type
 */
public final class ASTNodeFunctionDispatcher<T> {
	private final IASTNodeFunction<T> mFunc;
	
	/**
	 * @param func
	 *            AST node function.
	 */
	public ASTNodeFunctionDispatcher(final IASTNodeFunction<T> func) {
		mFunc = func;
	}
	
	/**
	 * @param arrayModifier
	 *            AST array modifier.
	 * @return result
	 */
	public T dispatch(final IASTArrayModifier arrayModifier) {
		if (arrayModifier instanceof ICASTArrayModifier) {
			return mFunc.on((ICASTArrayModifier) arrayModifier);
		}
		return mFunc.on(arrayModifier);
	}
	
	/**
	 * @param attributeSpecifier
	 *            AST attribute specifier.
	 * @return result
	 */
	public T dispatch(final IASTAttributeSpecifier attributeSpecifier) {
		if (attributeSpecifier instanceof IGCCASTAttributeSpecifier) {
			return mFunc.on((IGCCASTAttributeSpecifier) attributeSpecifier);
		}
		return mFunc.on(attributeSpecifier);
	}
	
	/**
	 * @param declaration
	 *            AST declaration.
	 * @return result
	 */
	public T dispatch(final IASTDeclaration declaration) {
		if (declaration instanceof IASTSimpleDeclaration) {
			return mFunc.on((IASTSimpleDeclaration) declaration);
		} else if (declaration instanceof IASTFunctionDefinition) {
			return mFunc.on((IASTFunctionDefinition) declaration);
		} else if (declaration instanceof IASTProblemDeclaration) {
			return mFunc.on((IASTProblemDeclaration) declaration);
		} else if (declaration instanceof IASTASMDeclaration) {
			return mFunc.on((IASTASMDeclaration) declaration);
		} else {
			return mFunc.on(declaration);
		}
	}
	
	/**
	 * @param declarator
	 *            AST declarator.
	 * @return result
	 */
	public T dispatch(final IASTDeclarator declarator) {
		if (declarator instanceof IASTFunctionDeclarator) {
			if (declarator instanceof IASTStandardFunctionDeclarator) {
				return mFunc.on((IASTStandardFunctionDeclarator) declarator);
			} else if (declarator instanceof ICASTKnRFunctionDeclarator) {
				return mFunc.on((ICASTKnRFunctionDeclarator) declarator);
			} else {
				return mFunc.on((IASTFunctionDeclarator) declarator);
			}
		} else if (declarator instanceof IASTArrayDeclarator) {
			return mFunc.on((IASTArrayDeclarator) declarator);
		} else if (declarator instanceof IASTFieldDeclarator) {
			return mFunc.on((IASTFieldDeclarator) declarator);
		} else {
			return mFunc.on(declarator);
		}
	}
	
	/**
	 * @param declSpecifier
	 *            AST declaration specifier.
	 * @return result
	 */
	public T dispatch(final IASTDeclSpecifier declSpecifier) {
		if (declSpecifier instanceof IASTSimpleDeclSpecifier) {
			return mFunc.on((IASTSimpleDeclSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTNamedTypeSpecifier) {
			return mFunc.on((IASTNamedTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTElaboratedTypeSpecifier) {
			return mFunc.on((IASTElaboratedTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTCompositeTypeSpecifier) {
			return mFunc.on((IASTCompositeTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTEnumerationSpecifier) {
			return mFunc.on((IASTEnumerationSpecifier) declSpecifier);
		} else {
			return mFunc.on(declSpecifier);
		}
	}
	
	/**
	 * @param expression
	 *            AST expression.
	 * @return result
	 */
	@SuppressWarnings("squid:MethodCyclomaticComplexity")
	public T dispatch(final IASTExpression expression) {
		if (expression instanceof IASTIdExpression) {
			return mFunc.on((IASTIdExpression) expression);
		} else if (expression instanceof IASTUnaryExpression) {
			return mFunc.on((IASTUnaryExpression) expression);
		} else if (expression instanceof IASTLiteralExpression) {
			return mFunc.on((IASTLiteralExpression) expression);
		} else if (expression instanceof IASTBinaryExpression) {
			return mFunc.on((IASTBinaryExpression) expression);
		} else if (expression instanceof IASTFieldReference) {
			return mFunc.on((IASTFieldReference) expression);
		} else if (expression instanceof IASTArraySubscriptExpression) {
			return mFunc.on((IASTArraySubscriptExpression) expression);
		} else if (expression instanceof IASTFunctionCallExpression) {
			return mFunc.on((IASTFunctionCallExpression) expression);
		} else if (expression instanceof IASTCastExpression) {
			return mFunc.on((IASTCastExpression) expression);
		} else if (expression instanceof IASTConditionalExpression) {
			return mFunc.on((IASTConditionalExpression) expression);
		} else if (expression instanceof IASTExpressionList) {
			return mFunc.on((IASTExpressionList) expression);
		} else if (expression instanceof IASTTypeIdExpression) {
			return mFunc.on((IASTTypeIdExpression) expression);
		} else if (expression instanceof IASTProblemExpression) {
			return mFunc.on((IASTProblemExpression) expression);
		} else if (expression instanceof IGNUASTCompoundStatementExpression) {
			return mFunc.on((IGNUASTCompoundStatementExpression) expression);
		} else if (expression instanceof IASTTypeIdInitializerExpression) {
			return mFunc.on((IASTTypeIdInitializerExpression) expression);
		} else if (expression instanceof IASTBinaryTypeIdExpression) {
			return mFunc.on((IASTBinaryTypeIdExpression) expression);
		} else {
			return mFunc.on(expression);
		}
	}
	
	/**
	 * @param initializer
	 *            AST initializer.
	 * @return result
	 */
	public T dispatch(final IASTInitializer initializer) {
		if (initializer instanceof IASTEqualsInitializer) {
			return mFunc.on((IASTEqualsInitializer) initializer);
		} else if (initializer instanceof IASTInitializerList) {
			return mFunc.on((IASTInitializerList) initializer);
		} else if (initializer instanceof ICASTDesignatedInitializer) {
			return mFunc.on((ICASTDesignatedInitializer) initializer);
		} else {
			return mFunc.on(initializer);
		}
	}
	
	/**
	 * @param name
	 *            AST name.
	 * @return result
	 */
	public T dispatch(final IASTName name) {
		if (name instanceof IASTImplicitName) {
			if (name instanceof IASTImplicitDestructorName) {
				return mFunc.on((IASTImplicitDestructorName) name);
			}
			return mFunc.on((IASTImplicitName) name);
		}
		return mFunc.on(name);
	}
	
	/**
	 * Invokes the function on the actual node type.
	 *
	 * @param node
	 *            node to call the function for
	 * @return the functions return value
	 */
	@SuppressWarnings("squid:MethodCyclomaticComplexity")
	public T dispatch(final IASTNode node) {
		if (node instanceof IASTExpression) {
			return dispatch((IASTExpression) node);
		} else if (node instanceof IASTName) {
			return dispatch((IASTName) node);
		} else if (node instanceof IASTStatement) {
			return dispatch((IASTStatement) node);
		} else if (node instanceof IASTDeclSpecifier) {
			return dispatch((IASTDeclSpecifier) node);
		} else if (node instanceof IASTDeclarator) {
			return dispatch((IASTDeclarator) node);
		} else if (node instanceof IASTPreprocessorMacroExpansion) {
			return mFunc.on((IASTPreprocessorMacroExpansion) node);
		} else if (node instanceof IASTTypeId) {
			return dispatch((IASTTypeId) node);
		} else if (node instanceof IASTComment) {
			return mFunc.on((IASTComment) node);
		} else if (node instanceof IASTDeclaration) {
			return dispatch((IASTDeclaration) node);
		} else if (node instanceof IASTParameterDeclaration) {
			return mFunc.on((IASTParameterDeclaration) node);
		} else if (node instanceof IASTPointerOperator) {
			return dispatch((IASTPointerOperator) node);
		} else if (node instanceof IASTPreprocessorStatement) {
			return dispatch((IASTPreprocessorStatement) node);
		} else if (node instanceof IASTInitializer) {
			return dispatch((IASTInitializer) node);
		} else if (node instanceof IASTEnumerator) {
			return mFunc.on((IASTEnumerator) node);
		} else if (node instanceof IASTArrayModifier) {
			return dispatch((IASTArrayModifier) node);
		} else if (node instanceof ICASTDesignator) {
			return dispatch((ICASTDesignator) node);
		} else if (node instanceof IASTProblem) {
			return mFunc.on((IASTProblem) node);
		} else if (node instanceof IASTTranslationUnit) {
			return mFunc.on((IASTTranslationUnit) node);
		} else if (node instanceof IASTToken) {
			return dispatch((IASTToken) node);
		} else if (node instanceof IASTAttributeSpecifier) {
			return dispatch((IASTAttributeSpecifier) node);
		} else if (node instanceof IASTAlignmentSpecifier) {
			return mFunc.on((IASTAlignmentSpecifier) node);
		} else if (node instanceof IASTAttribute) {
			return mFunc.on((IASTAttribute) node);
		} else {
			return mFunc.on(node);
		}
	}
	
	/**
	 * @param pointerOperator
	 *            AST pointer operator.
	 * @return result
	 */
	public T dispatch(final IASTPointerOperator pointerOperator) {
		if (pointerOperator instanceof IASTPointer) {
			if (pointerOperator instanceof ICASTPointer) {
				return mFunc.on((ICASTPointer) pointerOperator);
			}
			return mFunc.on((IASTPointer) pointerOperator);
		}
		return mFunc.on(pointerOperator);
	}
	
	/**
	 * @param preprocessorStatement
	 *            AST preprocessor statement.
	 * @return result
	 */
	@SuppressWarnings("squid:MethodCyclomaticComplexity")
	public T dispatch(final IASTPreprocessorStatement preprocessorStatement) {
		if (preprocessorStatement instanceof IASTPreprocessorEndifStatement) {
			return mFunc.on((IASTPreprocessorEndifStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorMacroDefinition) {
			if (preprocessorStatement instanceof IASTPreprocessorObjectStyleMacroDefinition) {
				return mFunc.on((IASTPreprocessorObjectStyleMacroDefinition) preprocessorStatement);
			} else if (preprocessorStatement instanceof IASTPreprocessorFunctionStyleMacroDefinition) {
				return mFunc.on((IASTPreprocessorFunctionStyleMacroDefinition) preprocessorStatement);
			} else {
				return mFunc.on((IASTPreprocessorMacroDefinition) preprocessorStatement);
			}
		} else if (preprocessorStatement instanceof IASTPreprocessorIfStatement) {
			return mFunc.on((IASTPreprocessorIfStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorElseStatement) {
			return mFunc.on((IASTPreprocessorElseStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIfdefStatement) {
			return mFunc.on((IASTPreprocessorIfdefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIfndefStatement) {
			return mFunc.on((IASTPreprocessorIfndefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIncludeStatement) {
			return mFunc.on((IASTPreprocessorIncludeStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorUndefStatement) {
			return mFunc.on((IASTPreprocessorUndefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorElifStatement) {
			return mFunc.on((IASTPreprocessorElifStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorPragmaStatement) {
			return mFunc.on((IASTPreprocessorPragmaStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorErrorStatement) {
			return mFunc.on((IASTPreprocessorErrorStatement) preprocessorStatement);
		} else {
			return mFunc.on(preprocessorStatement);
		}
	}
	
	/**
	 * @param statement
	 *            AST statement.
	 * @return result
	 */
	@SuppressWarnings("squid:MethodCyclomaticComplexity")
	public T dispatch(final IASTStatement statement) {
		if (statement instanceof IASTExpressionStatement) {
			return mFunc.on((IASTExpressionStatement) statement);
		} else if (statement instanceof IASTIfStatement) {
			return mFunc.on((IASTIfStatement) statement);
		} else if (statement instanceof IASTCompoundStatement) {
			return mFunc.on((IASTCompoundStatement) statement);
		} else if (statement instanceof IASTDeclarationStatement) {
			return mFunc.on((IASTDeclarationStatement) statement);
		} else if (statement instanceof IASTReturnStatement) {
			return mFunc.on((IASTReturnStatement) statement);
		} else if (statement instanceof IASTCaseStatement) {
			return mFunc.on((IASTCaseStatement) statement);
		} else if (statement instanceof IASTGotoStatement) {
			return mFunc.on((IASTGotoStatement) statement);
		} else if (statement instanceof IASTLabelStatement) {
			return mFunc.on((IASTLabelStatement) statement);
		} else if (statement instanceof IASTBreakStatement) {
			return mFunc.on((IASTBreakStatement) statement);
		} else if (statement instanceof IASTForStatement) {
			return mFunc.on((IASTForStatement) statement);
		} else if (statement instanceof IASTDoStatement) {
			return mFunc.on((IASTDoStatement) statement);
		} else if (statement instanceof IASTNullStatement) {
			return mFunc.on((IASTNullStatement) statement);
		} else if (statement instanceof IASTSwitchStatement) {
			return mFunc.on((IASTSwitchStatement) statement);
		} else if (statement instanceof IASTDefaultStatement) {
			return mFunc.on((IASTDefaultStatement) statement);
		} else if (statement instanceof IASTWhileStatement) {
			return mFunc.on((IASTWhileStatement) statement);
		} else if (statement instanceof IASTContinueStatement) {
			return mFunc.on((IASTContinueStatement) statement);
		} else if (statement instanceof IASTProblemStatement) {
			return mFunc.on((IASTProblemStatement) statement);
		} else if (statement instanceof IGNUASTGotoStatement) {
			return mFunc.on((IGNUASTGotoStatement) statement);
		} else {
			return mFunc.on(statement);
		}
	}
	
	/**
	 * @param token
	 *            AST token.
	 * @return result
	 */
	public T dispatch(final IASTToken token) {
		if (token instanceof IASTTokenList) {
			return mFunc.on((IASTTokenList) token);
		}
		return mFunc.on(token);
	}
	
	/**
	 * @param typeId
	 *            AST type ID.
	 * @return result
	 */
	public T dispatch(final IASTTypeId typeId) {
		if (typeId instanceof IASTProblemTypeId) {
			return mFunc.on((IASTProblemTypeId) typeId);
		}
		return mFunc.on(typeId);
	}
	
	/**
	 * @param castDesignator
	 *            CAST designator.
	 * @return result
	 */
	public T dispatch(final ICASTDesignator castDesignator) {
		if (castDesignator instanceof ICASTFieldDesignator) {
			return mFunc.on((ICASTFieldDesignator) castDesignator);
		} else if (castDesignator instanceof ICASTArrayDesignator) {
			return mFunc.on((ICASTArrayDesignator) castDesignator);
		} else if (castDesignator instanceof IGCCASTArrayRangeDesignator) {
			return mFunc.on((IGCCASTArrayRangeDesignator) castDesignator);
		} else {
			return mFunc.on(castDesignator);
		}
	}
	
	/**
	 * Invokes the function by using an ASTVisitor instead of multiple instanceof checks in order to detect the first
	 * first level of subtypes faster.
	 * Note that this is not the default implementation of dispatch(), because calling IASTNode.accept() is not
	 * guaranteed to be concurency safe. The caller has to explicitly decide if calling IASTNode methods is safe.
	 *
	 * @param node
	 *            node to call the function for
	 * @return the functions return value
	 */
	public T dispatchByVisitor(final IASTNode node) {
		return new DispatchVisitor(node).dispatchByVisitor();
	}
	
	/**
	 * Visitor for dispatching.
	 */
	private final class DispatchVisitor extends ASTVisitor {
		private final IASTNode mExpectedNode;
		private Optional<T> mResult = Optional.empty();
		
		DispatchVisitor(final IASTNode expectedNode) {
			// Visit everything that can be visited to get exactly one call to
			// visit whenever possible
			super(true);
			shouldVisitAmbiguousNodes = false;
			includeInactiveNodes = true;
			shouldVisitImplicitNames = true;
			shouldVisitTokens = true;
			
			// We need to make sure that the visit() overload is actually called
			// for the node we want and not a child, though
			mExpectedNode = expectedNode;
		}
		
		/**
		 * @return Dispatch result.
		 */
		public T dispatchByVisitor() {
			mExpectedNode.accept(this);
			return mResult.orElseGet(this::dispatchNonVisitedNode);
		}
		
		private T dispatchNonVisitedNode() {
			if (mExpectedNode instanceof IASTPreprocessorMacroExpansion) {
				return mFunc.on((IASTPreprocessorMacroExpansion) mExpectedNode);
			} else if (mExpectedNode instanceof IASTComment) {
				return mFunc.on((IASTComment) mExpectedNode);
			} else if (mExpectedNode instanceof IASTPreprocessorStatement) {
				return dispatch((IASTPreprocessorStatement) mExpectedNode);
			} else if (mExpectedNode instanceof IASTProblem) {
				return mFunc.on((IASTProblem) mExpectedNode);
			} else if (mExpectedNode instanceof IASTAlignmentSpecifier) {
				return mFunc.on((IASTAlignmentSpecifier) mExpectedNode);
			} else {
				return mFunc.on(mExpectedNode);
			}
		}
		
		@Override
		public int visit(final IASTArrayModifier arrayModifier) {
			if (mExpectedNode.equals(arrayModifier)) {
				mResult = Optional.of(dispatch(arrayModifier));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTAttribute attribute) {
			if (mExpectedNode.equals(attribute)) {
				mResult = Optional.of(mFunc.on(attribute));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTAttributeSpecifier attributeSpecifier) {
			if (mExpectedNode.equals(attributeSpecifier)) {
				mResult = Optional.of(dispatch(attributeSpecifier));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTDeclaration declaration) {
			if (mExpectedNode.equals(declaration)) {
				mResult = Optional.of(dispatch(declaration));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTDeclarator declarator) {
			if (mExpectedNode.equals(declarator)) {
				mResult = Optional.of(dispatch(declarator));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTDeclSpecifier declSpecifier) {
			if (mExpectedNode.equals(declSpecifier)) {
				mResult = Optional.of(dispatch(declSpecifier));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTEnumerator enumerator) {
			if (mExpectedNode.equals(enumerator)) {
				mResult = Optional.of(mFunc.on(enumerator));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTExpression expression) {
			if (mExpectedNode.equals(expression)) {
				mResult = Optional.of(dispatch(expression));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTInitializer initializer) {
			if (mExpectedNode.equals(initializer)) {
				mResult = Optional.of(dispatch(initializer));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTName name) {
			if (mExpectedNode.equals(name)) {
				mResult = Optional.of(dispatch(name));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTParameterDeclaration parameterDeclaration) {
			if (mExpectedNode.equals(parameterDeclaration)) {
				mResult = Optional.of(mFunc.on(parameterDeclaration));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTPointerOperator pointerOperator) {
			if (mExpectedNode.equals(pointerOperator)) {
				mResult = Optional.of(dispatch(pointerOperator));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTProblem problem) {
			if (mExpectedNode.equals(problem)) {
				mResult = Optional.of(mFunc.on(problem));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTStatement statement) {
			if (mExpectedNode.equals(statement)) {
				mResult = Optional.of(dispatch(statement));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTToken token) {
			if (mExpectedNode.equals(token)) {
				mResult = Optional.of(dispatch(token));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTTranslationUnit translationUnit) {
			if (mExpectedNode.equals(translationUnit)) {
				mResult = Optional.of(mFunc.on(translationUnit));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTTypeId typeId) {
			if (mExpectedNode.equals(typeId)) {
				mResult = Optional.of(dispatch(typeId));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICASTDesignator castDesignator) {
			if (mExpectedNode.equals(castDesignator)) {
				mResult = Optional.of(dispatch(castDesignator));
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICPPASTBaseSpecifier cppBaseSpecifier) {
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICPPASTCapture cppCapture) {
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICPPASTClassVirtSpecifier cppClassVirtSpecifier) {
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICPPASTDecltypeSpecifier cppDecltypeSpecifier) {
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICPPASTNamespaceDefinition cppNamespaceDefinition) {
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICPPASTTemplateParameter cppTemplateParameter) {
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICPPASTVirtSpecifier cppVirtSpecifier) {
			return PROCESS_ABORT;
		}
	}
}
