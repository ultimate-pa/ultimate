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

public final class ASTNodeConsumerDispatcher {
	final IASTNodeConsumer consumer;

	public ASTNodeConsumerDispatcher(IASTNodeConsumer consumer) {
		this.consumer = consumer;
	}

	public void dispatch(IASTArrayModifier arrayModifier) {
		if (arrayModifier instanceof ICASTArrayModifier) {
			consumer.on((ICASTArrayModifier) arrayModifier);
		} else {
			consumer.on(arrayModifier);
		}
	}

	public void dispatch(IASTAttributeSpecifier attributeSpecifier) {
		if (attributeSpecifier instanceof IGCCASTAttributeSpecifier) {
			consumer.on((IGCCASTAttributeSpecifier) attributeSpecifier);
		} else {
			consumer.on(attributeSpecifier);
		}
	}

	public void dispatch(IASTDeclSpecifier declSpecifier) {
		if (declSpecifier instanceof IASTSimpleDeclSpecifier) {
			consumer.on((IASTSimpleDeclSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTNamedTypeSpecifier) {
			consumer.on((IASTNamedTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTElaboratedTypeSpecifier) {
			consumer.on((IASTElaboratedTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTCompositeTypeSpecifier) {
			consumer.on((IASTCompositeTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTEnumerationSpecifier) {
			consumer.on((IASTEnumerationSpecifier) declSpecifier);
		} else {
			consumer.on(declSpecifier);
		}
	}

	public void dispatch(IASTDeclaration declaration) {
		if (declaration instanceof IASTSimpleDeclaration) {
			consumer.on((IASTSimpleDeclaration) declaration);
		} else if (declaration instanceof IASTFunctionDefinition) {
			consumer.on((IASTFunctionDefinition) declaration);
		} else if (declaration instanceof IASTProblemDeclaration) {
			consumer.on((IASTProblemDeclaration) declaration);
		} else if (declaration instanceof IASTASMDeclaration) {
			consumer.on((IASTASMDeclaration) declaration);
		} else {
			consumer.on(declaration);
		}
	}

	public void dispatch(IASTDeclarator declarator) {
		if (declarator instanceof IASTFunctionDeclarator) {
			if (declarator instanceof IASTStandardFunctionDeclarator) {
				consumer.on((IASTStandardFunctionDeclarator) declarator);
			} else if (declarator instanceof ICASTKnRFunctionDeclarator) {
				consumer.on((ICASTKnRFunctionDeclarator) declarator);
			} else {
				consumer.on((IASTFunctionDeclarator) declarator);
			}
		} else if (declarator instanceof IASTArrayDeclarator) {
			consumer.on((IASTArrayDeclarator) declarator);
		} else if (declarator instanceof IASTFieldDeclarator) {
			consumer.on((IASTFieldDeclarator) declarator);
		} else {
			consumer.on(declarator);
		}
	}

	public void dispatch(IASTExpression expression) {
		if (expression instanceof IASTIdExpression) {
			consumer.on((IASTIdExpression) expression);
		} else if (expression instanceof IASTUnaryExpression) {
			consumer.on((IASTUnaryExpression) expression);
		} else if (expression instanceof IASTLiteralExpression) {
			consumer.on((IASTLiteralExpression) expression);
		} else if (expression instanceof IASTBinaryExpression) {
			consumer.on((IASTBinaryExpression) expression);
		} else if (expression instanceof IASTFieldReference) {
			consumer.on((IASTFieldReference) expression);
		} else if (expression instanceof IASTArraySubscriptExpression) {
			consumer.on((IASTArraySubscriptExpression) expression);
		} else if (expression instanceof IASTFunctionCallExpression) {
			consumer.on((IASTFunctionCallExpression) expression);
		} else if (expression instanceof IASTCastExpression) {
			consumer.on((IASTCastExpression) expression);
		} else if (expression instanceof IASTConditionalExpression) {
			consumer.on((IASTConditionalExpression) expression);
		} else if (expression instanceof IASTExpressionList) {
			consumer.on((IASTExpressionList) expression);
		} else if (expression instanceof IASTTypeIdExpression) {
			consumer.on((IASTTypeIdExpression) expression);
		} else if (expression instanceof IASTProblemExpression) {
			consumer.on((IASTProblemExpression) expression);
		} else if (expression instanceof IGNUASTCompoundStatementExpression) {
			consumer.on((IGNUASTCompoundStatementExpression) expression);
		} else if (expression instanceof IASTTypeIdInitializerExpression) {
			consumer.on((IASTTypeIdInitializerExpression) expression);
		} else if (expression instanceof IASTBinaryTypeIdExpression) {
			consumer.on((IASTBinaryTypeIdExpression) expression);
		} else {
			consumer.on(expression);
		}
	}

	public void dispatch(IASTInitializer initializer) {
		if (initializer instanceof IASTEqualsInitializer) {
			consumer.on((IASTEqualsInitializer) initializer);
		} else if (initializer instanceof IASTInitializerList) {
			consumer.on((IASTInitializerList) initializer);
		} else if (initializer instanceof ICASTDesignatedInitializer) {
			consumer.on((ICASTDesignatedInitializer) initializer);
		} else {
			consumer.on(initializer);
		}
	}

	public void dispatch(IASTName name) {
		if (name instanceof IASTImplicitName) {
			if (name instanceof IASTImplicitDestructorName) {
				consumer.on((IASTImplicitDestructorName) name);
			} else {
				consumer.on((IASTImplicitName) name);
			}
		} else {
			consumer.on(name);
		}
	}

	public void dispatch(IASTPointerOperator pointerOperator) {
		if (pointerOperator instanceof IASTPointer) {
			if (pointerOperator instanceof ICASTPointer) {
				consumer.on((ICASTPointer) pointerOperator);
			} else {
				consumer.on((IASTPointer) pointerOperator);
			}
		} else {
			consumer.on(pointerOperator);
		}
	}

	public void dispatch(IASTPreprocessorStatement preprocessorStatement) {
		if (preprocessorStatement instanceof IASTPreprocessorEndifStatement) {
			consumer.on((IASTPreprocessorEndifStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorMacroDefinition) {
			if (preprocessorStatement instanceof IASTPreprocessorObjectStyleMacroDefinition) {
				consumer.on((IASTPreprocessorObjectStyleMacroDefinition) preprocessorStatement);
			} else if (preprocessorStatement instanceof IASTPreprocessorFunctionStyleMacroDefinition) {
				consumer.on((IASTPreprocessorFunctionStyleMacroDefinition) preprocessorStatement);
			} else {
				consumer.on((IASTPreprocessorMacroDefinition) preprocessorStatement);
			}
		} else if (preprocessorStatement instanceof IASTPreprocessorIfStatement) {
			consumer.on((IASTPreprocessorIfStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorElseStatement) {
			consumer.on((IASTPreprocessorElseStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIfdefStatement) {
			consumer.on((IASTPreprocessorIfdefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIfndefStatement) {
			consumer.on((IASTPreprocessorIfndefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIncludeStatement) {
			consumer.on((IASTPreprocessorIncludeStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorUndefStatement) {
			consumer.on((IASTPreprocessorUndefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorElifStatement) {
			consumer.on((IASTPreprocessorElifStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorPragmaStatement) {
			consumer.on((IASTPreprocessorPragmaStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorErrorStatement) {
			consumer.on((IASTPreprocessorErrorStatement) preprocessorStatement);
		} else {
			consumer.on(preprocessorStatement);
		}
	}

	public void dispatch(IASTStatement statement) {
		if (statement instanceof IASTExpressionStatement) {
			consumer.on((IASTExpressionStatement) statement);
		} else if (statement instanceof IASTIfStatement) {
			consumer.on((IASTIfStatement) statement);
		} else if (statement instanceof IASTCompoundStatement) {
			consumer.on((IASTCompoundStatement) statement);
		} else if (statement instanceof IASTDeclarationStatement) {
			consumer.on((IASTDeclarationStatement) statement);
		} else if (statement instanceof IASTReturnStatement) {
			consumer.on((IASTReturnStatement) statement);
		} else if (statement instanceof IASTCaseStatement) {
			consumer.on((IASTCaseStatement) statement);
		} else if (statement instanceof IASTGotoStatement) {
			consumer.on((IASTGotoStatement) statement);
		} else if (statement instanceof IASTLabelStatement) {
			consumer.on((IASTLabelStatement) statement);
		} else if (statement instanceof IASTBreakStatement) {
			consumer.on((IASTBreakStatement) statement);
		} else if (statement instanceof IASTForStatement) {
			consumer.on((IASTForStatement) statement);
		} else if (statement instanceof IASTDoStatement) {
			consumer.on((IASTDoStatement) statement);
		} else if (statement instanceof IASTNullStatement) {
			consumer.on((IASTNullStatement) statement);
		} else if (statement instanceof IASTSwitchStatement) {
			consumer.on((IASTSwitchStatement) statement);
		} else if (statement instanceof IASTDefaultStatement) {
			consumer.on((IASTDefaultStatement) statement);
		} else if (statement instanceof IASTWhileStatement) {
			consumer.on((IASTWhileStatement) statement);
		} else if (statement instanceof IASTContinueStatement) {
			consumer.on((IASTContinueStatement) statement);
		} else if (statement instanceof IASTProblemStatement) {
			consumer.on((IASTProblemStatement) statement);
		} else if (statement instanceof IGNUASTGotoStatement) {
			consumer.on((IGNUASTGotoStatement) statement);
		} else {
			consumer.on(statement);
		}
	}

	public void dispatch(IASTToken token) {
		if (token instanceof IASTTokenList) {
			consumer.on((IASTTokenList) token);
		} else {
			consumer.on(token);
		}
	}

	public void dispatch(IASTTypeId typeId) {
		if (typeId instanceof IASTProblemTypeId) {
			consumer.on((IASTProblemTypeId) typeId);
		} else {
			consumer.on(typeId);
		}
	}

	public void dispatch(ICASTDesignator cDesignator) {
		if (cDesignator instanceof ICASTFieldDesignator) {
			consumer.on((ICASTFieldDesignator) cDesignator);
		} else if (cDesignator instanceof ICASTArrayDesignator) {
			consumer.on((ICASTArrayDesignator) cDesignator);
		} else if (cDesignator instanceof IGCCASTArrayRangeDesignator) {
			consumer.on((IGCCASTArrayRangeDesignator) cDesignator);
		} else {
			consumer.on(cDesignator);
		}
	}

	/**
	 * Invokes the function.
	 */
	public void dispatch(IASTNode node) {
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
			consumer.on((IASTPreprocessorMacroExpansion) node);
		} else if (node instanceof IASTTypeId) {
			dispatch((IASTTypeId) node);
		} else if (node instanceof IASTComment) {
			consumer.on((IASTComment) node);
		} else if (node instanceof IASTDeclaration) {
			dispatch((IASTDeclaration) node);
		} else if (node instanceof IASTParameterDeclaration) {
			consumer.on((IASTParameterDeclaration) node);
		} else if (node instanceof IASTPointerOperator) {
			dispatch((IASTPointerOperator) node);
		} else if (node instanceof IASTPreprocessorStatement) {
			dispatch((IASTPreprocessorStatement) node);
		} else if (node instanceof IASTInitializer) {
			dispatch((IASTInitializer) node);
		} else if (node instanceof IASTEnumerator) {
			consumer.on((IASTEnumerator) node);
		} else if (node instanceof IASTArrayModifier) {
			dispatch((IASTArrayModifier) node);
		} else if (node instanceof ICASTDesignator) {
			dispatch((ICASTDesignator) node);
		} else if (node instanceof IASTProblem) {
			consumer.on((IASTProblem) node);
		} else if (node instanceof IASTTranslationUnit) {
			consumer.on((IASTTranslationUnit) node);
		} else if (node instanceof IASTToken) {
			dispatch((IASTToken) node);
		} else if (node instanceof IASTAttributeSpecifier) {
			dispatch((IASTAttributeSpecifier) node);
		} else if (node instanceof IASTAlignmentSpecifier) {
			consumer.on((IASTAlignmentSpecifier) node);
		} else if (node instanceof IASTAttribute) {
			consumer.on((IASTAttribute) node);
		} else {
			consumer.on(node);
		}
	}

	/**
	 * Invokes the function by using an ASTVisitor instead of multiple
	 * instanceof checks in order to detect the first first level of subtypes
	 * faster.
	 *
	 * Note that this is not the default implementation of dispatch(), because
	 * calling IASTNode.accept() is not guaranteed to be concurency safe. The
	 * caller has to explicitly decide if calling IASTNode methods is safe.
	 */
	public void dispatchByVisitor(IASTNode node) {
		new DispatchVisitor(node).dispatchByVisitor();
	}

	private final class DispatchVisitor extends ASTVisitor {
		final IASTNode expectedNode;
		boolean dispatched = false;

		DispatchVisitor(IASTNode expectedNode) {
			// Visit everything that can be visited to get exactly one call to
			// visit whenever possible
			super(true);
			shouldVisitAmbiguousNodes = false;
			includeInactiveNodes = true;
			shouldVisitImplicitNames = true;
			shouldVisitTokens = true;

			// We need to make sure that the visit() overload is actually called
			// for the node we want and not a child, though
			this.expectedNode = expectedNode;
		}

		public void dispatchByVisitor() {
			expectedNode.accept(this);
			if (!dispatched) {
				dispatchNonVisitedNode();
			}
		}

		private void dispatchNonVisitedNode() {
			if (expectedNode instanceof IASTPreprocessorMacroExpansion) {
				consumer.on((IASTPreprocessorMacroExpansion) expectedNode);
			} else if (expectedNode instanceof IASTComment) {
				consumer.on((IASTComment) expectedNode);
			} else if (expectedNode instanceof IASTPreprocessorStatement) {
				dispatch((IASTPreprocessorStatement) expectedNode);
			} else if (expectedNode instanceof IASTProblem) {
				consumer.on((IASTProblem) expectedNode);
			} else if (expectedNode instanceof IASTAlignmentSpecifier) {
				consumer.on((IASTAlignmentSpecifier) expectedNode);
			} else {
				consumer.on(expectedNode);
			}
		}

		@Override
		public int visit(IASTArrayModifier arrayModifier) {
			if (expectedNode == arrayModifier) {
				dispatch(arrayModifier);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTAttribute attribute) {
			if (expectedNode == attribute) {
				consumer.on(attribute);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTAttributeSpecifier attributeSpecifier) {
			if (expectedNode == attributeSpecifier) {
				dispatch(attributeSpecifier);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTDeclSpecifier declSpecifier) {
			if (expectedNode == declSpecifier) {
				dispatch(declSpecifier);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTDeclaration declaration) {
			if (expectedNode == declaration) {
				dispatch(declaration);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTDeclarator declarator) {
			if (expectedNode == declarator) {
				dispatch(declarator);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTEnumerator enumerator) {
			if (expectedNode == enumerator) {
				consumer.on(enumerator);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTExpression expression) {
			if (expectedNode == expression) {
				dispatch(expression);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTInitializer initializer) {
			if (expectedNode == initializer) {
				dispatch(initializer);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTName name) {
			if (expectedNode == name) {
				dispatch(name);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTParameterDeclaration parameterDeclaration) {
			if (expectedNode == parameterDeclaration) {
				consumer.on(parameterDeclaration);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTPointerOperator pointerOperator) {
			if (expectedNode == pointerOperator) {
				dispatch(pointerOperator);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTProblem problem) {
			if (expectedNode == problem) {
				consumer.on(problem);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTStatement statement) {
			if (expectedNode == statement) {
				dispatch(statement);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTToken token) {
			if (expectedNode == token) {
				dispatch(token);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTTranslationUnit translationUnit) {
			if (expectedNode == translationUnit) {
				consumer.on(translationUnit);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IASTTypeId typeId) {
			if (expectedNode == typeId) {
				dispatch(typeId);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(ICASTDesignator cDesignator) {
			if (expectedNode == cDesignator) {
				dispatch(cDesignator);
				dispatched = true;
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(ICPPASTBaseSpecifier cppBaseSpecifier) {
			return PROCESS_ABORT;
		}

		@Override
		public int visit(ICPPASTCapture cppCapture) {
			return PROCESS_ABORT;
		}

		@Override
		public int visit(ICPPASTClassVirtSpecifier cppClassVirtSpecifier) {
			return PROCESS_ABORT;
		}

		@Override
		public int visit(ICPPASTDecltypeSpecifier cppDecltypeSpecifier) {
			return PROCESS_ABORT;
		}

		@Override
		public int visit(ICPPASTNamespaceDefinition cppNamespaceDefinition) {
			return PROCESS_ABORT;
		}

		@Override
		public int visit(ICPPASTTemplateParameter cppTemplateParameter) {
			return PROCESS_ABORT;
		}

		@Override
		public int visit(ICPPASTVirtSpecifier cppVirtSpecifier) {
			return PROCESS_ABORT;
		}

	}
}