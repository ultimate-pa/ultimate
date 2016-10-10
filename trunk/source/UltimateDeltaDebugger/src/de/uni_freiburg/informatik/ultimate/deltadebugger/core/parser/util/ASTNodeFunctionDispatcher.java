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

public final class ASTNodeFunctionDispatcher<T> {
	private final class DispatchVisitor extends ASTVisitor {
		final IASTNode expectedNode;
		Optional<T> result = Optional.empty();

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
			this.expectedNode = expectedNode;
		}

		public T dispatchByVisitor() {
			expectedNode.accept(this);
			return result.orElseGet(this::dispatchNonVisitedNode);
		}

		private T dispatchNonVisitedNode() {
			if (expectedNode instanceof IASTPreprocessorMacroExpansion) {
				return func.on((IASTPreprocessorMacroExpansion) expectedNode);
			} else if (expectedNode instanceof IASTComment) {
				return func.on((IASTComment) expectedNode);
			} else if (expectedNode instanceof IASTPreprocessorStatement) {
				return dispatch((IASTPreprocessorStatement) expectedNode);
			} else if (expectedNode instanceof IASTProblem) {
				return func.on((IASTProblem) expectedNode);
			} else if (expectedNode instanceof IASTAlignmentSpecifier) {
				return func.on((IASTAlignmentSpecifier) expectedNode);
			} else {
				return func.on(expectedNode);
			}
		}

		@Override
		public int visit(final IASTArrayModifier arrayModifier) {
			if (expectedNode == arrayModifier) {
				result = Optional.of(dispatch(arrayModifier));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTAttribute attribute) {
			if (expectedNode == attribute) {
				result = Optional.of(func.on(attribute));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTAttributeSpecifier attributeSpecifier) {
			if (expectedNode == attributeSpecifier) {
				result = Optional.of(dispatch(attributeSpecifier));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTDeclaration declaration) {
			if (expectedNode == declaration) {
				result = Optional.of(dispatch(declaration));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTDeclarator declarator) {
			if (expectedNode == declarator) {
				result = Optional.of(dispatch(declarator));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTDeclSpecifier declSpecifier) {
			if (expectedNode == declSpecifier) {
				result = Optional.of(dispatch(declSpecifier));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTEnumerator enumerator) {
			if (expectedNode == enumerator) {
				result = Optional.of(func.on(enumerator));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTExpression expression) {
			if (expectedNode == expression) {
				result = Optional.of(dispatch(expression));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTInitializer initializer) {
			if (expectedNode == initializer) {
				result = Optional.of(dispatch(initializer));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTName name) {
			if (expectedNode == name) {
				result = Optional.of(dispatch(name));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTParameterDeclaration parameterDeclaration) {
			if (expectedNode == parameterDeclaration) {
				result = Optional.of(func.on(parameterDeclaration));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTPointerOperator pointerOperator) {
			if (expectedNode == pointerOperator) {
				result = Optional.of(dispatch(pointerOperator));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTProblem problem) {
			if (expectedNode == problem) {
				result = Optional.of(func.on(problem));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTStatement statement) {
			if (expectedNode == statement) {
				result = Optional.of(dispatch(statement));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTToken token) {
			if (expectedNode == token) {
				result = Optional.of(dispatch(token));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTTranslationUnit translationUnit) {
			if (expectedNode == translationUnit) {
				result = Optional.of(func.on(translationUnit));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IASTTypeId typeId) {
			if (expectedNode == typeId) {
				result = Optional.of(dispatch(typeId));
			}
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final ICASTDesignator cDesignator) {
			if (expectedNode == cDesignator) {
				result = Optional.of(dispatch(cDesignator));
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

	final IASTNodeFunction<T> func;

	public ASTNodeFunctionDispatcher(final IASTNodeFunction<T> func) {
		this.func = func;
	}

	public T dispatch(final IASTArrayModifier arrayModifier) {
		if (arrayModifier instanceof ICASTArrayModifier) {
			return func.on((ICASTArrayModifier) arrayModifier);
		} else {
			return func.on(arrayModifier);
		}
	}

	public T dispatch(final IASTAttributeSpecifier attributeSpecifier) {
		if (attributeSpecifier instanceof IGCCASTAttributeSpecifier) {
			return func.on((IGCCASTAttributeSpecifier) attributeSpecifier);
		} else {
			return func.on(attributeSpecifier);
		}
	}

	public T dispatch(final IASTDeclaration declaration) {
		if (declaration instanceof IASTSimpleDeclaration) {
			return func.on((IASTSimpleDeclaration) declaration);
		} else if (declaration instanceof IASTFunctionDefinition) {
			return func.on((IASTFunctionDefinition) declaration);
		} else if (declaration instanceof IASTProblemDeclaration) {
			return func.on((IASTProblemDeclaration) declaration);
		} else if (declaration instanceof IASTASMDeclaration) {
			return func.on((IASTASMDeclaration) declaration);
		} else {
			return func.on(declaration);
		}
	}

	public T dispatch(final IASTDeclarator declarator) {
		if (declarator instanceof IASTFunctionDeclarator) {
			if (declarator instanceof IASTStandardFunctionDeclarator) {
				return func.on((IASTStandardFunctionDeclarator) declarator);
			} else if (declarator instanceof ICASTKnRFunctionDeclarator) {
				return func.on((ICASTKnRFunctionDeclarator) declarator);
			} else {
				return func.on((IASTFunctionDeclarator) declarator);
			}
		} else if (declarator instanceof IASTArrayDeclarator) {
			return func.on((IASTArrayDeclarator) declarator);
		} else if (declarator instanceof IASTFieldDeclarator) {
			return func.on((IASTFieldDeclarator) declarator);
		} else {
			return func.on(declarator);
		}
	}

	public T dispatch(final IASTDeclSpecifier declSpecifier) {
		if (declSpecifier instanceof IASTSimpleDeclSpecifier) {
			return func.on((IASTSimpleDeclSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTNamedTypeSpecifier) {
			return func.on((IASTNamedTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTElaboratedTypeSpecifier) {
			return func.on((IASTElaboratedTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTCompositeTypeSpecifier) {
			return func.on((IASTCompositeTypeSpecifier) declSpecifier);
		} else if (declSpecifier instanceof IASTEnumerationSpecifier) {
			return func.on((IASTEnumerationSpecifier) declSpecifier);
		} else {
			return func.on(declSpecifier);
		}
	}

	public T dispatch(final IASTExpression expression) {
		if (expression instanceof IASTIdExpression) {
			return func.on((IASTIdExpression) expression);
		} else if (expression instanceof IASTUnaryExpression) {
			return func.on((IASTUnaryExpression) expression);
		} else if (expression instanceof IASTLiteralExpression) {
			return func.on((IASTLiteralExpression) expression);
		} else if (expression instanceof IASTBinaryExpression) {
			return func.on((IASTBinaryExpression) expression);
		} else if (expression instanceof IASTFieldReference) {
			return func.on((IASTFieldReference) expression);
		} else if (expression instanceof IASTArraySubscriptExpression) {
			return func.on((IASTArraySubscriptExpression) expression);
		} else if (expression instanceof IASTFunctionCallExpression) {
			return func.on((IASTFunctionCallExpression) expression);
		} else if (expression instanceof IASTCastExpression) {
			return func.on((IASTCastExpression) expression);
		} else if (expression instanceof IASTConditionalExpression) {
			return func.on((IASTConditionalExpression) expression);
		} else if (expression instanceof IASTExpressionList) {
			return func.on((IASTExpressionList) expression);
		} else if (expression instanceof IASTTypeIdExpression) {
			return func.on((IASTTypeIdExpression) expression);
		} else if (expression instanceof IASTProblemExpression) {
			return func.on((IASTProblemExpression) expression);
		} else if (expression instanceof IGNUASTCompoundStatementExpression) {
			return func.on((IGNUASTCompoundStatementExpression) expression);
		} else if (expression instanceof IASTTypeIdInitializerExpression) {
			return func.on((IASTTypeIdInitializerExpression) expression);
		} else if (expression instanceof IASTBinaryTypeIdExpression) {
			return func.on((IASTBinaryTypeIdExpression) expression);
		} else {
			return func.on(expression);
		}
	}

	public T dispatch(final IASTInitializer initializer) {
		if (initializer instanceof IASTEqualsInitializer) {
			return func.on((IASTEqualsInitializer) initializer);
		} else if (initializer instanceof IASTInitializerList) {
			return func.on((IASTInitializerList) initializer);
		} else if (initializer instanceof ICASTDesignatedInitializer) {
			return func.on((ICASTDesignatedInitializer) initializer);
		} else {
			return func.on(initializer);
		}
	}

	public T dispatch(final IASTName name) {
		if (name instanceof IASTImplicitName) {
			if (name instanceof IASTImplicitDestructorName) {
				return func.on((IASTImplicitDestructorName) name);
			} else {
				return func.on((IASTImplicitName) name);
			}
		} else {
			return func.on(name);
		}
	}

	/**
	 * Invokes the function.
	 */
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
			return func.on((IASTPreprocessorMacroExpansion) node);
		} else if (node instanceof IASTTypeId) {
			return dispatch((IASTTypeId) node);
		} else if (node instanceof IASTComment) {
			return func.on((IASTComment) node);
		} else if (node instanceof IASTDeclaration) {
			return dispatch((IASTDeclaration) node);
		} else if (node instanceof IASTParameterDeclaration) {
			return func.on((IASTParameterDeclaration) node);
		} else if (node instanceof IASTPointerOperator) {
			return dispatch((IASTPointerOperator) node);
		} else if (node instanceof IASTPreprocessorStatement) {
			return dispatch((IASTPreprocessorStatement) node);
		} else if (node instanceof IASTInitializer) {
			return dispatch((IASTInitializer) node);
		} else if (node instanceof IASTEnumerator) {
			return func.on((IASTEnumerator) node);
		} else if (node instanceof IASTArrayModifier) {
			return dispatch((IASTArrayModifier) node);
		} else if (node instanceof ICASTDesignator) {
			return dispatch((ICASTDesignator) node);
		} else if (node instanceof IASTProblem) {
			return func.on((IASTProblem) node);
		} else if (node instanceof IASTTranslationUnit) {
			return func.on((IASTTranslationUnit) node);
		} else if (node instanceof IASTToken) {
			return dispatch((IASTToken) node);
		} else if (node instanceof IASTAttributeSpecifier) {
			return dispatch((IASTAttributeSpecifier) node);
		} else if (node instanceof IASTAlignmentSpecifier) {
			return func.on((IASTAlignmentSpecifier) node);
		} else if (node instanceof IASTAttribute) {
			return func.on((IASTAttribute) node);
		} else {
			return func.on(node);
		}
	}

	public T dispatch(final IASTPointerOperator pointerOperator) {
		if (pointerOperator instanceof IASTPointer) {
			if (pointerOperator instanceof ICASTPointer) {
				return func.on((ICASTPointer) pointerOperator);
			} else {
				return func.on((IASTPointer) pointerOperator);
			}
		} else {
			return func.on(pointerOperator);
		}
	}

	public T dispatch(final IASTPreprocessorStatement preprocessorStatement) {
		if (preprocessorStatement instanceof IASTPreprocessorEndifStatement) {
			return func.on((IASTPreprocessorEndifStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorMacroDefinition) {
			if (preprocessorStatement instanceof IASTPreprocessorObjectStyleMacroDefinition) {
				return func.on((IASTPreprocessorObjectStyleMacroDefinition) preprocessorStatement);
			} else if (preprocessorStatement instanceof IASTPreprocessorFunctionStyleMacroDefinition) {
				return func.on((IASTPreprocessorFunctionStyleMacroDefinition) preprocessorStatement);
			} else {
				return func.on((IASTPreprocessorMacroDefinition) preprocessorStatement);
			}
		} else if (preprocessorStatement instanceof IASTPreprocessorIfStatement) {
			return func.on((IASTPreprocessorIfStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorElseStatement) {
			return func.on((IASTPreprocessorElseStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIfdefStatement) {
			return func.on((IASTPreprocessorIfdefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIfndefStatement) {
			return func.on((IASTPreprocessorIfndefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorIncludeStatement) {
			return func.on((IASTPreprocessorIncludeStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorUndefStatement) {
			return func.on((IASTPreprocessorUndefStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorElifStatement) {
			return func.on((IASTPreprocessorElifStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorPragmaStatement) {
			return func.on((IASTPreprocessorPragmaStatement) preprocessorStatement);
		} else if (preprocessorStatement instanceof IASTPreprocessorErrorStatement) {
			return func.on((IASTPreprocessorErrorStatement) preprocessorStatement);
		} else {
			return func.on(preprocessorStatement);
		}
	}

	public T dispatch(final IASTStatement statement) {
		if (statement instanceof IASTExpressionStatement) {
			return func.on((IASTExpressionStatement) statement);
		} else if (statement instanceof IASTIfStatement) {
			return func.on((IASTIfStatement) statement);
		} else if (statement instanceof IASTCompoundStatement) {
			return func.on((IASTCompoundStatement) statement);
		} else if (statement instanceof IASTDeclarationStatement) {
			return func.on((IASTDeclarationStatement) statement);
		} else if (statement instanceof IASTReturnStatement) {
			return func.on((IASTReturnStatement) statement);
		} else if (statement instanceof IASTCaseStatement) {
			return func.on((IASTCaseStatement) statement);
		} else if (statement instanceof IASTGotoStatement) {
			return func.on((IASTGotoStatement) statement);
		} else if (statement instanceof IASTLabelStatement) {
			return func.on((IASTLabelStatement) statement);
		} else if (statement instanceof IASTBreakStatement) {
			return func.on((IASTBreakStatement) statement);
		} else if (statement instanceof IASTForStatement) {
			return func.on((IASTForStatement) statement);
		} else if (statement instanceof IASTDoStatement) {
			return func.on((IASTDoStatement) statement);
		} else if (statement instanceof IASTNullStatement) {
			return func.on((IASTNullStatement) statement);
		} else if (statement instanceof IASTSwitchStatement) {
			return func.on((IASTSwitchStatement) statement);
		} else if (statement instanceof IASTDefaultStatement) {
			return func.on((IASTDefaultStatement) statement);
		} else if (statement instanceof IASTWhileStatement) {
			return func.on((IASTWhileStatement) statement);
		} else if (statement instanceof IASTContinueStatement) {
			return func.on((IASTContinueStatement) statement);
		} else if (statement instanceof IASTProblemStatement) {
			return func.on((IASTProblemStatement) statement);
		} else if (statement instanceof IGNUASTGotoStatement) {
			return func.on((IGNUASTGotoStatement) statement);
		} else {
			return func.on(statement);
		}
	}

	public T dispatch(final IASTToken token) {
		if (token instanceof IASTTokenList) {
			return func.on((IASTTokenList) token);
		} else {
			return func.on(token);
		}
	}

	public T dispatch(final IASTTypeId typeId) {
		if (typeId instanceof IASTProblemTypeId) {
			return func.on((IASTProblemTypeId) typeId);
		} else {
			return func.on(typeId);
		}
	}

	public T dispatch(final ICASTDesignator cDesignator) {
		if (cDesignator instanceof ICASTFieldDesignator) {
			return func.on((ICASTFieldDesignator) cDesignator);
		} else if (cDesignator instanceof ICASTArrayDesignator) {
			return func.on((ICASTArrayDesignator) cDesignator);
		} else if (cDesignator instanceof IGCCASTArrayRangeDesignator) {
			return func.on((IGCCASTArrayRangeDesignator) cDesignator);
		} else {
			return func.on(cDesignator);
		}
	}

	/**
	 * Invokes the function by using an ASTVisitor instead of multiple instanceof checks in order to detect the first
	 * first level of subtypes faster.
	 *
	 * Note that this is not the default implementation of dispatch(), because calling IASTNode.accept() is not
	 * guaranteed to be concurency safe. The caller has to explicitly decide if calling IASTNode methods is safe.
	 */
	public T dispatchByVisitor(final IASTNode node) {
		return new DispatchVisitor(node).dispatchByVisitor();
	}
}