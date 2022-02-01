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
 * overload of an IASTNodeConsumer object.
 * Note: The idea of this class is to move the complexity out of the rest of the code, that needs to detect the runtime
 * type of an IASTNode.
 * <p>
 * The Cyclomatic Complexity (and other complexity metrics) cannot be reduced without artificially obfuscating the code.
 */
public final class ASTNodeConsumerDispatcher {
	private final IASTNodeConsumer mConsumer;
	
	/**
	 * @param consumer
	 *            AST node consumer.
	 */
	public ASTNodeConsumerDispatcher(final IASTNodeConsumer consumer) {
		mConsumer = consumer;
	}
	
	/**
	 * @param arrayModifier
	 *            AST array modifier.
	 */
	public void dispatch(final IASTArrayModifier arrayModifier) {
		if (arrayModifier instanceof ICASTArrayModifier) {
			mConsumer.on((ICASTArrayModifier) arrayModifier);
		} else {
			mConsumer.on(arrayModifier);
		}
	}
	
	/**
	 * @param attributeSpecifier
	 *            AST .
	 */
	public void dispatch(final IASTAttributeSpecifier attributeSpecifier) {
		if (attributeSpecifier instanceof IGCCASTAttributeSpecifier) {
			mConsumer.on((IGCCASTAttributeSpecifier) attributeSpecifier);
		} else {
			mConsumer.on(attributeSpecifier);
		}
	}
	
	/**
	 * @param declaration
	 *            AST declaration.
	 */
	public void dispatch(final IASTDeclaration declaration) {
		if (declaration instanceof IASTSimpleDeclaration) {
			mConsumer.on((IASTSimpleDeclaration) declaration);
		} else if (declaration instanceof IASTFunctionDefinition) {
			mConsumer.on((IASTFunctionDefinition) declaration);
		} else if (declaration instanceof IASTProblemDeclaration) {
			mConsumer.on((IASTProblemDeclaration) declaration);
		} else if (declaration instanceof IASTASMDeclaration) {
			mConsumer.on((IASTASMDeclaration) declaration);
		} else {
			mConsumer.on(declaration);
		}
	}
	
	/**
	 * @param declarator
	 *            AST declarator.
	 */
	public void dispatch(final IASTDeclarator declarator) {
		if (declarator instanceof IASTFunctionDeclarator) {
			if (declarator instanceof IASTStandardFunctionDeclarator) {
				mConsumer.on((IASTStandardFunctionDeclarator) declarator);
			} else if (declarator instanceof ICASTKnRFunctionDeclarator) {
				mConsumer.on((ICASTKnRFunctionDeclarator) declarator);
			} else {
				mConsumer.on((IASTFunctionDeclarator) declarator);
			}
		} else if (declarator instanceof IASTArrayDeclarator) {
			mConsumer.on((IASTArrayDeclarator) declarator);
		} else if (declarator instanceof IASTFieldDeclarator) {
			mConsumer.on((IASTFieldDeclarator) declarator);
		} else {
			mConsumer.on(declarator);
		}
	}
	
	/**
	 * @param declSpecifier
	 *            AST declaration specifier.
	 */
	public void dispatch(final IASTDeclSpecifier declSpecifier) {
		if (declSpecifier instanceof IASTSimpleDeclSpecifier) {
			mConsumer.on((IASTSimpleDeclSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTNamedTypeSpecifier) {
			mConsumer.on((IASTNamedTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTElaboratedTypeSpecifier) {
			mConsumer.on((IASTElaboratedTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTCompositeTypeSpecifier) {
			mConsumer.on((IASTCompositeTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTEnumerationSpecifier) {
			mConsumer.on((IASTEnumerationSpecifier) declSpecifier);
		} else {
			mConsumer.on(declSpecifier);
		}
	}
	
	/**
	 * @param expression
	 *            AST expression.
	 */
	@SuppressWarnings("squid:MethodCyclomaticComplexity")
	public void dispatch(final IASTExpression expression) {
		if (expression instanceof IASTIdExpression) {
			mConsumer.on((IASTIdExpression) expression);
		} else if (expression instanceof IASTUnaryExpression) {
			mConsumer.on((IASTUnaryExpression) expression);
		} else if (expression instanceof IASTLiteralExpression) {
			mConsumer.on((IASTLiteralExpression) expression);
		} else if (expression instanceof IASTBinaryExpression) {
			mConsumer.on((IASTBinaryExpression) expression);
		} else if (expression instanceof IASTFieldReference) {
			mConsumer.on((IASTFieldReference) expression);
		} else if (expression instanceof IASTArraySubscriptExpression) {
			mConsumer.on((IASTArraySubscriptExpression) expression);
		} else if (expression instanceof IASTFunctionCallExpression) {
			mConsumer.on((IASTFunctionCallExpression) expression);
		} else if (expression instanceof IASTCastExpression) {
			mConsumer.on((IASTCastExpression) expression);
		} else if (expression instanceof IASTConditionalExpression) {
			mConsumer.on((IASTConditionalExpression) expression);
		} else if (expression instanceof IASTExpressionList) {
			mConsumer.on((IASTExpressionList) expression);
		} else if (expression instanceof IASTTypeIdExpression) {
			mConsumer.on((IASTTypeIdExpression) expression);
		} else if (expression instanceof IASTProblemExpression) {
			mConsumer.on((IASTProblemExpression) expression);
		} else if (expression instanceof IGNUASTCompoundStatementExpression) {
			mConsumer.on((IGNUASTCompoundStatementExpression) expression);
		} else if (expression instanceof IASTTypeIdInitializerExpression) {
			mConsumer.on((IASTTypeIdInitializerExpression) expression);
		} else if (expression instanceof IASTBinaryTypeIdExpression) {
			mConsumer.on((IASTBinaryTypeIdExpression) expression);
		} else {
			mConsumer.on(expression);
		}
	}
	
	/**
	 * @param initializer
	 *            AST initializer.
	 */
	public void dispatch(final IASTInitializer initializer) {
		if (initializer instanceof IASTEqualsInitializer) {
			mConsumer.on((IASTEqualsInitializer) initializer);
		} else if (initializer instanceof IASTInitializerList) {
			mConsumer.on((IASTInitializerList) initializer);
		} else if (initializer instanceof ICASTDesignatedInitializer) {
			mConsumer.on((ICASTDesignatedInitializer) initializer);
		} else {
			mConsumer.on(initializer);
		}
	}
	
	/**
	 * @param name
	 *            AST name.
	 */
	public void dispatch(final IASTName name) {
		if (name instanceof IASTImplicitName) {
			if (name instanceof IASTImplicitDestructorName) {
				mConsumer.on((IASTImplicitDestructorName) name);
			} else {
				mConsumer.on((IASTImplicitName) name);
			}
		} else {
			mConsumer.on(name);
		}
	}
	
	/**
	 * Invokes the function on the actual node type.
	 *
	 * @param node
	 *            node to call the function for
	 */
	@SuppressWarnings("squid:MethodCyclomaticComplexity")
	public void dispatch(final IASTNode node) {
		if (node instanceof IASTExpression) {
			dispatch((IASTExpression) node);
		} else if (node instanceof IASTName) {
			dispatch((IASTName) node);
		} else if (node instanceof IASTStatement) {
			dispatch((IASTStatement) node);
		} else if (node instanceof IASTDeclSpecifier) {
			dispatch((IASTDeclSpecifier) node);
		} else if (node instanceof IASTDeclarator) {
			dispatch((IASTDeclarator) node);
		} else if (node instanceof IASTPreprocessorMacroExpansion) {
			mConsumer.on((IASTPreprocessorMacroExpansion) node);
		} else if (node instanceof IASTTypeId) {
			dispatch((IASTTypeId) node);
		} else if (node instanceof IASTComment) {
			mConsumer.on((IASTComment) node);
		} else if (node instanceof IASTDeclaration) {
			dispatch((IASTDeclaration) node);
		} else if (node instanceof IASTParameterDeclaration) {
			mConsumer.on((IASTParameterDeclaration) node);
		} else if (node instanceof IASTPointerOperator) {
			dispatch((IASTPointerOperator) node);
		} else if (node instanceof IASTPreprocessorStatement) {
			dispatch((IASTPreprocessorStatement) node);
		} else if (node instanceof IASTInitializer) {
			dispatch((IASTInitializer) node);
		} else if (node instanceof IASTEnumerator) {
			mConsumer.on((IASTEnumerator) node);
		} else if (node instanceof IASTArrayModifier) {
			dispatch((IASTArrayModifier) node);
		} else if (node instanceof ICASTDesignator) {
			dispatch((ICASTDesignator) node);
		} else if (node instanceof IASTProblem) {
			mConsumer.on((IASTProblem) node);
		} else if (node instanceof IASTTranslationUnit) {
			mConsumer.on((IASTTranslationUnit) node);
		} else if (node instanceof IASTToken) {
			dispatch((IASTToken) node);
		} else if (node instanceof IASTAttributeSpecifier) {
			dispatch((IASTAttributeSpecifier) node);
		} else if (node instanceof IASTAlignmentSpecifier) {
			mConsumer.on((IASTAlignmentSpecifier) node);
		} else if (node instanceof IASTAttribute) {
			mConsumer.on((IASTAttribute) node);
		} else {
			mConsumer.on(node);
		}
	}
	
	/**
	 * @param pointerOperator
	 *            AST pointer operator.
	 */
	public void dispatch(final IASTPointerOperator pointerOperator) {
		if (pointerOperator instanceof IASTPointer) {
			if (pointerOperator instanceof ICASTPointer) {
				mConsumer.on((ICASTPointer) pointerOperator);
			} else {
				mConsumer.on((IASTPointer) pointerOperator);
			}
		} else {
			mConsumer.on(pointerOperator);
		}
	}
	
	/**
	 * @param preprocessorStatement
	 *            AST preprocessor statement.
	 */
	public void dispatch(final IASTPreprocessorStatement preprocessorStatement) {
		if (preprocessorStatement instanceof IASTPreprocessorEndifStatement) {
			mConsumer.on((IASTPreprocessorEndifStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorMacroDefinition) {
			if (preprocessorStatement instanceof IASTPreprocessorObjectStyleMacroDefinition) {
				mConsumer.on((IASTPreprocessorObjectStyleMacroDefinition) preprocessorStatement);
			} else if (preprocessorStatement instanceof IASTPreprocessorFunctionStyleMacroDefinition) {
				mConsumer.on((IASTPreprocessorFunctionStyleMacroDefinition) preprocessorStatement);
			} else {
				mConsumer.on((IASTPreprocessorMacroDefinition) preprocessorStatement);
			}
		} else if (preprocessorStatement instanceof IASTPreprocessorIfStatement) {
			mConsumer.on((IASTPreprocessorIfStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorElseStatement) {
			mConsumer.on((IASTPreprocessorElseStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIfdefStatement) {
			mConsumer.on((IASTPreprocessorIfdefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIfndefStatement) {
			mConsumer.on((IASTPreprocessorIfndefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIncludeStatement) {
			mConsumer.on((IASTPreprocessorIncludeStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorUndefStatement) {
			mConsumer.on((IASTPreprocessorUndefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorElifStatement) {
			mConsumer.on((IASTPreprocessorElifStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorPragmaStatement) {
			mConsumer.on((IASTPreprocessorPragmaStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorErrorStatement) {
			mConsumer.on((IASTPreprocessorErrorStatement) preprocessorStatement);
		} else {
			mConsumer.on(preprocessorStatement);
		}
	}
	
	/**
	 * @param statement
	 *            AST statement.
	 */
	@SuppressWarnings("squid:MethodCyclomaticComplexity")
	public void dispatch(final IASTStatement statement) {
		if (statement instanceof IASTExpressionStatement) {
			mConsumer.on((IASTExpressionStatement) statement);
		} else if (statement instanceof IASTIfStatement) {
			mConsumer.on((IASTIfStatement) statement);
		} else if (statement instanceof IASTCompoundStatement) {
			mConsumer.on((IASTCompoundStatement) statement);
		} else if (statement instanceof IASTDeclarationStatement) {
			mConsumer.on((IASTDeclarationStatement) statement);
		} else if (statement instanceof IASTReturnStatement) {
			mConsumer.on((IASTReturnStatement) statement);
		} else if (statement instanceof IASTCaseStatement) {
			mConsumer.on((IASTCaseStatement) statement);
		} else if (statement instanceof IASTGotoStatement) {
			mConsumer.on((IASTGotoStatement) statement);
		} else if (statement instanceof IASTLabelStatement) {
			mConsumer.on((IASTLabelStatement) statement);
		} else if (statement instanceof IASTBreakStatement) {
			mConsumer.on((IASTBreakStatement) statement);
		} else if (statement instanceof IASTForStatement) {
			mConsumer.on((IASTForStatement) statement);
		} else if (statement instanceof IASTDoStatement) {
			mConsumer.on((IASTDoStatement) statement);
		} else if (statement instanceof IASTNullStatement) {
			mConsumer.on((IASTNullStatement) statement);
		} else if (statement instanceof IASTSwitchStatement) {
			mConsumer.on((IASTSwitchStatement) statement);
		} else if (statement instanceof IASTDefaultStatement) {
			mConsumer.on((IASTDefaultStatement) statement);
		} else if (statement instanceof IASTWhileStatement) {
			mConsumer.on((IASTWhileStatement) statement);
		} else if (statement instanceof IASTContinueStatement) {
			mConsumer.on((IASTContinueStatement) statement);
		} else if (statement instanceof IASTProblemStatement) {
			mConsumer.on((IASTProblemStatement) statement);
		} else if (statement instanceof IGNUASTGotoStatement) {
			mConsumer.on((IGNUASTGotoStatement) statement);
		} else {
			mConsumer.on(statement);
		}
	}
	
	/**
	 * @param token
	 *            AST token.
	 */
	public void dispatch(final IASTToken token) {
		if (token instanceof IASTTokenList) {
			mConsumer.on((IASTTokenList) token);
		} else {
			mConsumer.on(token);
		}
	}
	
	/**
	 * @param typeId
	 *            AST type ID.
	 */
	public void dispatch(final IASTTypeId typeId) {
		if (typeId instanceof IASTProblemTypeId) {
			mConsumer.on((IASTProblemTypeId) typeId);
		} else {
			mConsumer.on(typeId);
		}
	}
	
	/**
	 * @param castDesignator
	 *            CAST designator.
	 */
	public void dispatch(final ICASTDesignator castDesignator) {
		if (castDesignator instanceof ICASTFieldDesignator) {
			mConsumer.on((ICASTFieldDesignator) castDesignator);
		} else if (castDesignator instanceof ICASTArrayDesignator) {
			mConsumer.on((ICASTArrayDesignator) castDesignator);
		} else if (castDesignator instanceof IGCCASTArrayRangeDesignator) {
			mConsumer.on((IGCCASTArrayRangeDesignator) castDesignator);
		} else {
			mConsumer.on(castDesignator);
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
	 */
	public void dispatchByVisitor(final IASTNode node) {
		new DispatchVisitor(node).dispatchByVisitor();
	}
	
	/**
	 * Visitor for dispatching.
	 */
	private final class DispatchVisitor extends ASTVisitor {
		private final IASTNode mExpectedNode;
		private boolean mDispatched;
		
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
		 * Dispatches.
		 */
		public void dispatchByVisitor() {
			mExpectedNode.accept(this);
			if (!mDispatched) {
				dispatchNonVisitedNode();
			}
		}
		
		private void dispatchNonVisitedNode() {
			if (mExpectedNode instanceof IASTPreprocessorMacroExpansion) {
				mConsumer.on((IASTPreprocessorMacroExpansion) mExpectedNode);
			} else if (mExpectedNode instanceof IASTComment) {
				mConsumer.on((IASTComment) mExpectedNode);
			} else if (mExpectedNode instanceof IASTPreprocessorStatement) {
				dispatch((IASTPreprocessorStatement) mExpectedNode);
			} else if (mExpectedNode instanceof IASTProblem) {
				mConsumer.on((IASTProblem) mExpectedNode);
			} else if (mExpectedNode instanceof IASTAlignmentSpecifier) {
				mConsumer.on((IASTAlignmentSpecifier) mExpectedNode);
			} else {
				mConsumer.on(mExpectedNode);
			}
		}
		
		@Override
		public int visit(final IASTArrayModifier arrayModifier) {
			if (mExpectedNode.equals(arrayModifier)) {
				dispatch(arrayModifier);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTAttribute attribute) {
			if (mExpectedNode.equals(attribute)) {
				mConsumer.on(attribute);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTAttributeSpecifier attributeSpecifier) {
			if (mExpectedNode.equals(attributeSpecifier)) {
				dispatch(attributeSpecifier);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTDeclaration declaration) {
			if (mExpectedNode.equals(declaration)) {
				dispatch(declaration);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTDeclarator declarator) {
			if (mExpectedNode.equals(declarator)) {
				dispatch(declarator);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTDeclSpecifier declSpecifier) {
			if (mExpectedNode.equals(declSpecifier)) {
				dispatch(declSpecifier);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTEnumerator enumerator) {
			if (mExpectedNode.equals(enumerator)) {
				mConsumer.on(enumerator);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTExpression expression) {
			if (mExpectedNode.equals(expression)) {
				dispatch(expression);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTInitializer initializer) {
			if (mExpectedNode.equals(initializer)) {
				dispatch(initializer);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTName name) {
			if (mExpectedNode.equals(name)) {
				dispatch(name);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTParameterDeclaration parameterDeclaration) {
			if (mExpectedNode.equals(parameterDeclaration)) {
				mConsumer.on(parameterDeclaration);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTPointerOperator pointerOperator) {
			if (mExpectedNode.equals(pointerOperator)) {
				dispatch(pointerOperator);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTProblem problem) {
			if (mExpectedNode.equals(problem)) {
				mConsumer.on(problem);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTStatement statement) {
			if (mExpectedNode.equals(statement)) {
				dispatch(statement);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTToken token) {
			if (mExpectedNode.equals(token)) {
				dispatch(token);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTTranslationUnit translationUnit) {
			if (mExpectedNode.equals(translationUnit)) {
				mConsumer.on(translationUnit);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final IASTTypeId typeId) {
			if (mExpectedNode.equals(typeId)) {
				dispatch(typeId);
				mDispatched = true;
			}
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(final ICASTDesignator castDesignator) {
			if (mExpectedNode.equals(castDesignator)) {
				dispatch(castDesignator);
				mDispatched = true;
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
