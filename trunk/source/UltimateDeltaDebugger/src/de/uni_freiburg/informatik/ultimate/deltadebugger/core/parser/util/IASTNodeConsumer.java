package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTAlignmentSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTAttribute;
import org.eclipse.cdt.core.dom.ast.IASTAttributeOwner;
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
import org.eclipse.cdt.core.dom.ast.IASTImplicitDestructorNameOwner;
import org.eclipse.cdt.core.dom.ast.IASTImplicitName;
import org.eclipse.cdt.core.dom.ast.IASTImplicitNameOwner;
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
import org.eclipse.cdt.core.dom.ast.gnu.IGCCASTAttributeSpecifier;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.gnu.c.IGCCASTArrayRangeDesignator;

/**
 * Simulates a double double dispatch function for an IASTNode argument.
 *
 * Extend this class and override the corresponding on() overloads to implement
 * specialized functions based on the runtime IASTNode type. Each on() overload
 * defaults to the overload for it's direct super type, e.g.
 * on(IASTBinaryExpression) calls on(IASTExpression) calls on(IASTNode) unless
 * overridden.
 * 
 * This code is generated to only support interfaces relevant for C code, i.e.
 * it does not support ICPPAST* interfaces. Certain ICAST* interfaces have been
 * removed as well, because they do not add new methods or cause problems
 * because of multiple inheritance.
 * 
 * The main reason for using this class is that the instanceof-mess and/or
 * visitor boilerplate is not part of the code containing actual logic anymore.
 * 
 * Note that there are multiple benefits over the original ASTVisitor:
 * 
 * * The visitor only supports part of the type hierarchy, e.g. it only has
 * overloads for IASTExpression but not for any subtypes like
 * IASTBinaryExpression.
 * 
 * * In those cases where it does support a subtype, the default visit()
 * implementation * will not be overriden if the user only overrides the visit()
 * of the supertype.
 * 
 * * The visitor does not support certain types at all, i.e. preprocessor nodes
 * 
 * However, it may come with a small performance penalty, if there are only few
 * overridden overloads. Especially if the JIT-compiler fails to remove
 * redundant branches that all end inside on(IASTNode) (I have no idea if it
 * does).
 * 
 * The comment of each overload also serves as a quick reference to the expected
 * properties a node may have in it's parent (not duplicated for subtypes).
 * 
 */
public interface IASTNodeConsumer {

	void on(IASTNode node);

	/**
	 * <pre>
	 * IASTAlignmentSpecifier.getPropertyInParent() values 
	 *   {@link IASTDeclSpecifier#ALIGNMENT_SPECIFIER}
	 *
	 * </pre>
	 */
	default void on(IASTAlignmentSpecifier alignmentSpecifier) {
		on((IASTNode) alignmentSpecifier);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(ICASTArrayModifier)}
	 *
	 * IASTArrayModifier.getPropertyInParent() values 
	 *   {@link IASTArrayDeclarator#ARRAY_MODIFIER}
	 *
	 * </pre>
	 */
	default void on(IASTArrayModifier arrayModifier) {
		on((IASTNode) arrayModifier);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTArrayModifier)}
	 *
	 */
	default void on(ICASTArrayModifier cArrayModifier) {
		on((IASTArrayModifier) cArrayModifier);
	}

	/**
	 * <pre>
	 * IASTAttribute.getPropertyInParent() values 
	 *   {@link IASTAttributeSpecifier#ATTRIBUTE}
	 *
	 * </pre>
	 */
	default void on(IASTAttribute attribute) {
		on((IASTNode) attribute);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IGCCASTAttributeSpecifier)}
	 *
	 * IASTAttributeSpecifier.getPropertyInParent() values 
	 *   {@link IASTAttributeOwner#ATTRIBUTE_SPECIFIER}
	 *
	 * </pre>
	 */
	default void on(IASTAttributeSpecifier attributeSpecifier) {
		on((IASTNode) attributeSpecifier);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTAttributeSpecifier)}
	 *
	 */
	default void on(IGCCASTAttributeSpecifier gccAttributeSpecifier) {
		on((IASTAttributeSpecifier) gccAttributeSpecifier);
	}

	/**
	 * <pre>
	 * IASTComment.getPropertyInParent() values 
	 *   {@link IASTTranslationUnit#PREPROCESSOR_STATEMENT}
	 *
	 * </pre>
	 */
	default void on(IASTComment comment) {
		on((IASTNode) comment);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTCompositeTypeSpecifier)}
	 *   {@link ASTNodeConsumer#on(IASTElaboratedTypeSpecifier)}
	 *   {@link ASTNodeConsumer#on(IASTEnumerationSpecifier)}
	 *   {@link ASTNodeConsumer#on(IASTNamedTypeSpecifier)}
	 *   {@link ASTNodeConsumer#on(IASTSimpleDeclSpecifier)}
	 *
	 * IASTDeclSpecifier.getPropertyInParent() values 
	 *   {@link IASTFunctionDefinition#DECL_SPECIFIER}
	 *   {@link IASTParameterDeclaration#DECL_SPECIFIER}
	 *   {@link IASTSimpleDeclaration#DECL_SPECIFIER}
	 *   {@link IASTTypeId#DECL_SPECIFIER}
	 *
	 * </pre>
	 */
	default void on(IASTDeclSpecifier declSpecifier) {
		on((IASTNode) declSpecifier);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}
	 *
	 */
	default void on(IASTCompositeTypeSpecifier compositeTypeSpecifier) {
		on((IASTDeclSpecifier) compositeTypeSpecifier);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}
	 *
	 */
	default void on(IASTElaboratedTypeSpecifier elaboratedTypeSpecifier) {
		on((IASTDeclSpecifier) elaboratedTypeSpecifier);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}
	 *
	 */
	default void on(IASTEnumerationSpecifier enumerationSpecifier) {
		on((IASTDeclSpecifier) enumerationSpecifier);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}
	 *
	 */
	default void on(IASTNamedTypeSpecifier namedTypeSpecifier) {
		on((IASTDeclSpecifier) namedTypeSpecifier);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}
	 *
	 */
	default void on(IASTSimpleDeclSpecifier simpleDeclSpecifier) {
		on((IASTDeclSpecifier) simpleDeclSpecifier);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTASMDeclaration)}
	 *   {@link ASTNodeConsumer#on(IASTFunctionDefinition)}
	 *   {@link ASTNodeConsumer#on(IASTProblemDeclaration)}
	 *   {@link ASTNodeConsumer#on(IASTSimpleDeclaration)}
	 *
	 * IASTDeclaration.getPropertyInParent() values 
	 *   {@link IASTCompositeTypeSpecifier#MEMBER_DECLARATION}
	 *   {@link IASTDeclarationStatement#DECLARATION}
	 *   {@link IASTIfStatement#CONDITION}
	 *   {@link IASTTranslationUnit#OWNED_DECLARATION}
	 *   {@link ICASTKnRFunctionDeclarator#FUNCTION_PARAMETER}
	 *
	 * </pre>
	 */
	default void on(IASTDeclaration declaration) {
		on((IASTNode) declaration);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclaration)}
	 *
	 */
	default void on(IASTASMDeclaration asmDeclaration) {
		on((IASTDeclaration) asmDeclaration);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclaration)}
	 *
	 */
	default void on(IASTFunctionDefinition functionDefinition) {
		on((IASTDeclaration) functionDefinition);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclaration)}
	 *
	 */
	default void on(IASTProblemDeclaration problemDeclaration) {
		on((IASTDeclaration) problemDeclaration);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclaration)}
	 *
	 */
	default void on(IASTSimpleDeclaration simpleDeclaration) {
		on((IASTDeclaration) simpleDeclaration);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTArrayDeclarator)}
	 *   {@link ASTNodeConsumer#on(IASTFieldDeclarator)}
	 *   {@link ASTNodeConsumer#on(IASTFunctionDeclarator)}
	 *
	 * IASTDeclarator.getPropertyInParent() values 
	 *   {@link IASTDeclarator#NESTED_DECLARATOR}
	 *   {@link IASTParameterDeclaration#DECLARATOR}
	 *   {@link IASTSimpleDeclaration#DECLARATOR}
	 *   {@link IASTTypeId#ABSTRACT_DECLARATOR}
	 *
	 * </pre>
	 */
	default void on(IASTDeclarator declarator) {
		on((IASTNode) declarator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclarator)}
	 *
	 */
	default void on(IASTArrayDeclarator arrayDeclarator) {
		on((IASTDeclarator) arrayDeclarator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclarator)}
	 *
	 */
	default void on(IASTFieldDeclarator fieldDeclarator) {
		on((IASTDeclarator) fieldDeclarator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclarator)}
	 *
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTStandardFunctionDeclarator)}
	 *   {@link ASTNodeConsumer#on(ICASTKnRFunctionDeclarator)}
	 *
	 * IASTFunctionDeclarator.getPropertyInParent() values 
	 *   {@link IASTFunctionDefinition#DECLARATOR}
	 *
	 * </pre>
	 */
	default void on(IASTFunctionDeclarator functionDeclarator) {
		on((IASTDeclarator) functionDeclarator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTFunctionDeclarator)}
	 *
	 */
	default void on(IASTStandardFunctionDeclarator standardFunctionDeclarator) {
		on((IASTFunctionDeclarator) standardFunctionDeclarator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTFunctionDeclarator)}
	 *
	 */
	default void on(ICASTKnRFunctionDeclarator cKnRFunctionDeclarator) {
		on((IASTFunctionDeclarator) cKnRFunctionDeclarator);
	}

	/**
	 * <pre>
	 * IASTEnumerator.getPropertyInParent() values 
	 *   {@link IASTEnumerationSpecifier#ENUMERATOR}
	 *
	 * </pre>
	 */
	default void on(IASTEnumerator enumerator) {
		on((IASTNode) enumerator);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTArraySubscriptExpression)}
	 *   {@link ASTNodeConsumer#on(IASTBinaryExpression)}
	 *   {@link ASTNodeConsumer#on(IASTBinaryTypeIdExpression)}
	 *   {@link ASTNodeConsumer#on(IASTCastExpression)}
	 *   {@link ASTNodeConsumer#on(IASTConditionalExpression)}
	 *   {@link ASTNodeConsumer#on(IASTExpressionList)}
	 *   {@link ASTNodeConsumer#on(IASTFieldReference)}
	 *   {@link ASTNodeConsumer#on(IASTFunctionCallExpression)}
	 *   {@link ASTNodeConsumer#on(IASTIdExpression)}
	 *   {@link ASTNodeConsumer#on(IASTLiteralExpression)}
	 *   {@link ASTNodeConsumer#on(IASTProblemExpression)}
	 *   {@link ASTNodeConsumer#on(IASTTypeIdExpression)}
	 *   {@link ASTNodeConsumer#on(IASTTypeIdInitializerExpression)}
	 *   {@link ASTNodeConsumer#on(IASTUnaryExpression)}
	 *   {@link ASTNodeConsumer#on(IGNUASTCompoundStatementExpression)}
	 *
	 * IASTExpression.getPropertyInParent() values 
	 *   {@link IASTAlignmentSpecifier#ALIGNMENT_EXPRESSION}
	 *   {@link IASTArrayModifier#CONSTANT_EXPRESSION}
	 *   {@link IASTArraySubscriptExpression#ARRAY}
	 *   {@link IASTArraySubscriptExpression#SUBSCRIPT}
	 *   {@link IASTBinaryExpression#OPERAND_ONE}
	 *   {@link IASTBinaryExpression#OPERAND_TWO}
	 *   {@link IASTCaseStatement#EXPRESSION}
	 *   {@link IASTCastExpression#OPERAND}
	 *   {@link IASTConditionalExpression#LOGICAL_CONDITION}
	 *   {@link IASTConditionalExpression#NEGATIVE_RESULT}
	 *   {@link IASTConditionalExpression#POSITIVE_RESULT}
	 *   {@link IASTDoStatement#CONDITION}
	 *   {@link IASTEnumerator#ENUMERATOR_VALUE}
	 *   {@link IASTEqualsInitializer#INITIALIZER}
	 *   {@link IASTExpressionList#NESTED_EXPRESSION}
	 *   {@link IASTExpressionStatement#EXPRESSION}
	 *   {@link IASTFieldDeclarator#FIELD_SIZE}
	 *   {@link IASTFieldReference#FIELD_OWNER}
	 *   {@link IASTForStatement#CONDITION}
	 *   {@link IASTForStatement#ITERATION}
	 *   {@link IASTFunctionCallExpression#ARGUMENT}
	 *   {@link IASTFunctionCallExpression#FUNCTION_NAME}
	 *   {@link IASTIfStatement#CONDITION}
	 *   {@link IASTInitializerList#NESTED_INITIALIZER}
	 *   {@link IASTReturnStatement#RETURNVALUE}
	 *   {@link IASTSimpleDeclSpecifier#DECLTYPE_EXPRESSION}
	 *   {@link IASTSwitchStatement#CONTROLLER_EXP}
	 *   {@link IASTUnaryExpression#OPERAND}
	 *   {@link IASTWhileStatement#CONDITIONEXPRESSION}
	 *   {@link ICASTArrayDesignator#SUBSCRIPT_EXPRESSION}
	 *   {@link ICASTDesignatedInitializer#OPERAND}
	 *   {@link IGCCASTArrayRangeDesignator#SUBSCRIPT_CEILING_EXPRESSION}
	 *   {@link IGCCASTArrayRangeDesignator#SUBSCRIPT_FLOOR_EXPRESSION}
	 *   {@link IGNUASTGotoStatement#LABEL_NAME}
	 *
	 * </pre>
	 */
	default void on(IASTExpression expression) {
		on((IASTNode) expression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTArraySubscriptExpression arraySubscriptExpression) {
		on((IASTExpression) arraySubscriptExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTBinaryExpression binaryExpression) {
		on((IASTExpression) binaryExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTBinaryTypeIdExpression binaryTypeIdExpression) {
		on((IASTExpression) binaryTypeIdExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTCastExpression castExpression) {
		on((IASTExpression) castExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTConditionalExpression conditionalExpression) {
		on((IASTExpression) conditionalExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTExpressionList expressionList) {
		on((IASTExpression) expressionList);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTFieldReference fieldReference) {
		on((IASTExpression) fieldReference);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTFunctionCallExpression functionCallExpression) {
		on((IASTExpression) functionCallExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTIdExpression idExpression) {
		on((IASTExpression) idExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTLiteralExpression literalExpression) {
		on((IASTExpression) literalExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTProblemExpression problemExpression) {
		on((IASTExpression) problemExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTTypeIdExpression typeIdExpression) {
		on((IASTExpression) typeIdExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTTypeIdInitializerExpression typeIdInitializerExpression) {
		on((IASTExpression) typeIdInitializerExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IASTUnaryExpression unaryExpression) {
		on((IASTExpression) unaryExpression);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}
	 *
	 */
	default void on(IGNUASTCompoundStatementExpression gnuCompoundStatementExpression) {
		on((IASTExpression) gnuCompoundStatementExpression);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTEqualsInitializer)}
	 *   {@link ASTNodeConsumer#on(IASTInitializerList)}
	 *   {@link ASTNodeConsumer#on(ICASTDesignatedInitializer)}
	 *
	 * IASTInitializer.getPropertyInParent() values 
	 *   {@link IASTDeclarator#INITIALIZER}
	 *   {@link IASTTypeIdInitializerExpression#INITIALIZER}
	 *
	 * </pre>
	 */
	default void on(IASTInitializer initializer) {
		on((IASTNode) initializer);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTInitializer)}
	 *
	 */
	default void on(IASTEqualsInitializer equalsInitializer) {
		on((IASTInitializer) equalsInitializer);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTInitializer)}
	 *
	 * <pre>
	 * IASTInitializerList.getPropertyInParent() values 
	 *   {@link IASTEqualsInitializer#INITIALIZER}
	 *   {@link IASTFunctionCallExpression#ARGUMENT}
	 *   {@link IASTInitializerList#NESTED_INITIALIZER}
	 *   {@link IASTReturnStatement#RETURNVALUE}
	 *   {@link ICASTDesignatedInitializer#OPERAND}
	 *
	 * </pre>
	 */
	default void on(IASTInitializerList initializerList) {
		on((IASTInitializer) initializerList);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTInitializer)}
	 *
	 * <pre>
	 * ICASTDesignatedInitializer.getPropertyInParent() values 
	 *   {@link IASTEqualsInitializer#INITIALIZER}
	 *   {@link IASTFunctionCallExpression#ARGUMENT}
	 *   {@link IASTInitializerList#NESTED_INITIALIZER}
	 *   {@link IASTReturnStatement#RETURNVALUE}
	 *   {@link ICASTDesignatedInitializer#OPERAND}
	 *
	 * </pre>
	 */
	default void on(ICASTDesignatedInitializer cDesignatedInitializer) {
		on((IASTInitializer) cDesignatedInitializer);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTImplicitName)}
	 *
	 * IASTName.getPropertyInParent() values 
	 *   {@link IASTCompositeTypeSpecifier#TYPE_NAME}
	 *   {@link IASTDeclarator#DECLARATOR_NAME}
	 *   {@link IASTElaboratedTypeSpecifier#TYPE_NAME}
	 *   {@link IASTEnumerationSpecifier#ENUMERATION_NAME}
	 *   {@link IASTEnumerator#ENUMERATOR_NAME}
	 *   {@link IASTFieldReference#FIELD_NAME}
	 *   {@link IASTGotoStatement#NAME}
	 *   {@link IASTIdExpression#ID_NAME}
	 *   {@link IASTLabelStatement#NAME}
	 *   {@link IASTNamedTypeSpecifier#NAME}
	 *   {@link IASTPreprocessorIncludeStatement#INCLUDE_NAME}
	 *   {@link IASTPreprocessorMacroDefinition#MACRO_NAME}
	 *   {@link IASTPreprocessorMacroExpansion#EXPANSION_NAME}
	 *   {@link IASTPreprocessorMacroExpansion#NESTED_EXPANSION_NAME}
	 *   {@link IASTPreprocessorStatement#MACRO_NAME}
	 *   {@link ICASTFieldDesignator#FIELD_NAME}
	 *   {@link ICASTKnRFunctionDeclarator#PARAMETER_NAME}
	 *
	 * </pre>
	 */
	default void on(IASTName name) {
		on((IASTNode) name);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTName)}
	 *
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTImplicitDestructorName)}
	 *
	 * IASTImplicitName.getPropertyInParent() values 
	 *   {@link IASTImplicitNameOwner#IMPLICIT_NAME}
	 *
	 * </pre>
	 */
	default void on(IASTImplicitName implicitName) {
		on((IASTName) implicitName);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTImplicitName)}
	 *
	 * <pre>
	 * IASTImplicitDestructorName.getPropertyInParent() values 
	 *   {@link IASTImplicitDestructorNameOwner#IMPLICIT_DESTRUCTOR_NAME}
	 *
	 * </pre>
	 */
	default void on(IASTImplicitDestructorName implicitDestructorName) {
		on((IASTImplicitName) implicitDestructorName);
	}

	/**
	 * <pre>
	 * IASTParameterDeclaration.getPropertyInParent() values 
	 *   {@link IASTStandardFunctionDeclarator#FUNCTION_PARAMETER}
	 *
	 * </pre>
	 */
	default void on(IASTParameterDeclaration parameterDeclaration) {
		on((IASTNode) parameterDeclaration);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTPointer)}
	 *
	 * IASTPointerOperator.getPropertyInParent() values 
	 *   {@link IASTDeclarator#POINTER_OPERATOR}
	 *
	 * </pre>
	 */
	default void on(IASTPointerOperator pointerOperator) {
		on((IASTNode) pointerOperator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPointerOperator)}
	 *
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(ICASTPointer)}
	 *
	 * </pre>
	 */
	default void on(IASTPointer pointer) {
		on((IASTPointerOperator) pointer);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPointer)}
	 *
	 */
	default void on(ICASTPointer cPointer) {
		on((IASTPointer) cPointer);
	}

	/**
	 * <pre>
	 * IASTPreprocessorMacroExpansion.getPropertyInParent() values 
	 *   {@link IASTTranslationUnit#MACRO_EXPANSION}
	 *
	 * </pre>
	 */
	default void on(IASTPreprocessorMacroExpansion preprocessorMacroExpansion) {
		on((IASTNode) preprocessorMacroExpansion);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorElifStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorElseStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorEndifStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorErrorStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorIfStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorIfdefStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorIfndefStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorIncludeStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorMacroDefinition)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorPragmaStatement)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorUndefStatement)}
	 *
	 * IASTPreprocessorStatement.getPropertyInParent() values 
	 *   {@link IASTTranslationUnit#PREPROCESSOR_STATEMENT}
	 *
	 * </pre>
	 */
	default void on(IASTPreprocessorStatement preprocessorStatement) {
		on((IASTNode) preprocessorStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorElifStatement preprocessorElifStatement) {
		on((IASTPreprocessorStatement) preprocessorElifStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorElseStatement preprocessorElseStatement) {
		on((IASTPreprocessorStatement) preprocessorElseStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorEndifStatement preprocessorEndifStatement) {
		on((IASTPreprocessorStatement) preprocessorEndifStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorErrorStatement preprocessorErrorStatement) {
		on((IASTPreprocessorStatement) preprocessorErrorStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorIfStatement preprocessorIfStatement) {
		on((IASTPreprocessorStatement) preprocessorIfStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorIfdefStatement preprocessorIfdefStatement) {
		on((IASTPreprocessorStatement) preprocessorIfdefStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorIfndefStatement preprocessorIfndefStatement) {
		on((IASTPreprocessorStatement) preprocessorIfndefStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorIncludeStatement preprocessorIncludeStatement) {
		on((IASTPreprocessorStatement) preprocessorIncludeStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorFunctionStyleMacroDefinition)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorObjectStyleMacroDefinition)}
	 *
	 * </pre>
	 */
	default void on(IASTPreprocessorMacroDefinition preprocessorMacroDefinition) {
		on((IASTPreprocessorStatement) preprocessorMacroDefinition);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorMacroDefinition)}
	 *
	 */
	default void on(IASTPreprocessorFunctionStyleMacroDefinition preprocessorFunctionStyleMacroDefinition) {
		on((IASTPreprocessorMacroDefinition) preprocessorFunctionStyleMacroDefinition);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorMacroDefinition)}
	 *
	 */
	default void on(IASTPreprocessorObjectStyleMacroDefinition preprocessorObjectStyleMacroDefinition) {
		on((IASTPreprocessorMacroDefinition) preprocessorObjectStyleMacroDefinition);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorPragmaStatement preprocessorPragmaStatement) {
		on((IASTPreprocessorStatement) preprocessorPragmaStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}
	 *
	 */
	default void on(IASTPreprocessorUndefStatement preprocessorUndefStatement) {
		on((IASTPreprocessorStatement) preprocessorUndefStatement);
	}

	/**
	 * <pre>
	 * IASTProblem.getPropertyInParent() values 
	 *   {@link IASTTranslationUnit#SCANNER_PROBLEM}
	 *
	 * </pre>
	 */
	default void on(IASTProblem problem) {
		on((IASTNode) problem);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTBreakStatement)}
	 *   {@link ASTNodeConsumer#on(IASTCaseStatement)}
	 *   {@link ASTNodeConsumer#on(IASTCompoundStatement)}
	 *   {@link ASTNodeConsumer#on(IASTContinueStatement)}
	 *   {@link ASTNodeConsumer#on(IASTDeclarationStatement)}
	 *   {@link ASTNodeConsumer#on(IASTDefaultStatement)}
	 *   {@link ASTNodeConsumer#on(IASTDoStatement)}
	 *   {@link ASTNodeConsumer#on(IASTExpressionStatement)}
	 *   {@link ASTNodeConsumer#on(IASTForStatement)}
	 *   {@link ASTNodeConsumer#on(IASTGotoStatement)}
	 *   {@link ASTNodeConsumer#on(IASTIfStatement)}
	 *   {@link ASTNodeConsumer#on(IASTLabelStatement)}
	 *   {@link ASTNodeConsumer#on(IASTNullStatement)}
	 *   {@link ASTNodeConsumer#on(IASTProblemStatement)}
	 *   {@link ASTNodeConsumer#on(IASTReturnStatement)}
	 *   {@link ASTNodeConsumer#on(IASTSwitchStatement)}
	 *   {@link ASTNodeConsumer#on(IASTWhileStatement)}
	 *   {@link ASTNodeConsumer#on(IGNUASTGotoStatement)}
	 *
	 * IASTStatement.getPropertyInParent() values 
	 *   {@link IASTCompoundStatement#NESTED_STATEMENT}
	 *   {@link IASTDoStatement#BODY}
	 *   {@link IASTForStatement#BODY}
	 *   {@link IASTForStatement#INITIALIZER}
	 *   {@link IASTFunctionDefinition#FUNCTION_BODY}
	 *   {@link IASTIfStatement#ELSE}
	 *   {@link IASTIfStatement#THEN}
	 *   {@link IASTLabelStatement#NESTED_STATEMENT}
	 *   {@link IASTSwitchStatement#BODY}
	 *   {@link IASTWhileStatement#BODY}
	 *
	 * </pre>
	 */
	default void on(IASTStatement statement) {
		on((IASTNode) statement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTBreakStatement breakStatement) {
		on((IASTStatement) breakStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTCaseStatement caseStatement) {
		on((IASTStatement) caseStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 * <pre>
	 * IASTCompoundStatement.getPropertyInParent() values 
	 *   {@link IGNUASTCompoundStatementExpression#STATEMENT}
	 *
	 * </pre>
	 */
	default void on(IASTCompoundStatement compoundStatement) {
		on((IASTStatement) compoundStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTContinueStatement continueStatement) {
		on((IASTStatement) continueStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTDeclarationStatement declarationStatement) {
		on((IASTStatement) declarationStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTDefaultStatement defaultStatement) {
		on((IASTStatement) defaultStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTDoStatement doStatement) {
		on((IASTStatement) doStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTExpressionStatement expressionStatement) {
		on((IASTStatement) expressionStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTForStatement forStatement) {
		on((IASTStatement) forStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTGotoStatement gotoStatement) {
		on((IASTStatement) gotoStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTIfStatement ifStatement) {
		on((IASTStatement) ifStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTLabelStatement labelStatement) {
		on((IASTStatement) labelStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTNullStatement nullStatement) {
		on((IASTStatement) nullStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTProblemStatement problemStatement) {
		on((IASTStatement) problemStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTReturnStatement returnStatement) {
		on((IASTStatement) returnStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTSwitchStatement switchStatement) {
		on((IASTStatement) switchStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IASTWhileStatement whileStatement) {
		on((IASTStatement) whileStatement);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}
	 *
	 */
	default void on(IGNUASTGotoStatement gnuGotoStatement) {
		on((IASTStatement) gnuGotoStatement);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTTokenList)}
	 *
	 * IASTToken.getPropertyInParent() values 
	 *   {@link IASTAttribute#ARGUMENT_CLAUSE}
	 *   {@link IASTTokenList#NESTED_TOKEN}
	 *
	 * </pre>
	 */
	default void on(IASTToken token) {
		on((IASTNode) token);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTToken)}
	 *
	 */
	default void on(IASTTokenList tokenList) {
		on((IASTToken) tokenList);
	}

	default void on(IASTTranslationUnit translationUnit) {
		on((IASTNode) translationUnit);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(IASTProblemTypeId)}
	 *
	 * IASTTypeId.getPropertyInParent() values 
	 *   {@link IASTAlignmentSpecifier#ALIGNMENT_TYPEID}
	 *   {@link IASTBinaryTypeIdExpression#OPERAND1}
	 *   {@link IASTBinaryTypeIdExpression#OPERAND2}
	 *   {@link IASTCastExpression#TYPE_ID}
	 *   {@link IASTTypeIdExpression#TYPE_ID}
	 *   {@link IASTTypeIdInitializerExpression#TYPE_ID}
	 *
	 * </pre>
	 */
	default void on(IASTTypeId typeId) {
		on((IASTNode) typeId);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTTypeId)}
	 *
	 */
	default void on(IASTProblemTypeId problemTypeId) {
		on((IASTTypeId) problemTypeId);
	}

	/**
	 * <pre>
	 * Overridden by 
	 *   {@link ASTNodeConsumer#on(ICASTArrayDesignator)}
	 *   {@link ASTNodeConsumer#on(ICASTFieldDesignator)}
	 *   {@link ASTNodeConsumer#on(IGCCASTArrayRangeDesignator)}
	 *
	 * ICASTDesignator.getPropertyInParent() values 
	 *   {@link ICASTDesignatedInitializer#DESIGNATOR}
	 *
	 * </pre>
	 */
	default void on(ICASTDesignator cDesignator) {
		on((IASTNode) cDesignator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(ICASTDesignator)}
	 *
	 */
	default void on(ICASTArrayDesignator cArrayDesignator) {
		on((ICASTDesignator) cArrayDesignator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(ICASTDesignator)}
	 *
	 */
	default void on(ICASTFieldDesignator cFieldDesignator) {
		on((ICASTDesignator) cFieldDesignator);
	}

	/**
	 * Overrides {@link ASTNodeConsumer#on(ICASTDesignator)}
	 *
	 */
	default void on(IGCCASTArrayRangeDesignator gccArrayRangeDesignator) {
		on((ICASTDesignator) gccArrayRangeDesignator);
	}

}
