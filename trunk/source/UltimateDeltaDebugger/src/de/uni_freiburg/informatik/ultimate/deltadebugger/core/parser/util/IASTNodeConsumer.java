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
 * Extend this class and override the corresponding on() overloads to implement specialized functions based on the
 * runtime IASTNode type. Each on() overload defaults to the overload for it's direct super type, e.g.
 * on(IASTBinaryExpression) calls on(IASTExpression) calls on(IASTNode) unless overridden.
 * This code is generated to only support interfaces relevant for C code, i.e. it does not support ICPPAST* interfaces.
 * Certain ICAST* interfaces have been removed as well, because they do not add new methods or cause problems because of
 * multiple inheritance.
 * The main reason for using this class is that the instanceof-mess and/or visitor boilerplate is not part of the code
 * containing actual logic anymore.
 * Note that there are multiple benefits over the original ASTVisitor:
 * * The visitor only supports part of the type hierarchy, e.g. it only has overloads for IASTExpression but not for any
 * subtypes like IASTBinaryExpression.
 * * In those cases where it does support a subtype, the default visit() implementation * will not be overriden if the
 * user only overrides the visit() of the supertype.
 * * The visitor does not support certain types at all, i.e. preprocessor nodes
 * However, it may come with a small performance penalty, if there are only few overridden overloads. Especially if the
 * JIT-compiler fails to remove redundant branches that all end inside on(IASTNode) (I have no idea if it does).
 * The comment of each overload also serves as a quick reference to the expected properties a node may have in it's
 * parent (not duplicated for subtypes).
 */
@FunctionalInterface
public interface IASTNodeConsumer {
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTAlignmentSpecifier.getPropertyInParent() values
	 *   {@link IASTDeclSpecifier#ALIGNMENT_SPECIFIER}
	 * </pre>
	 *
	 * @param alignmentSpecifier
	 *            alignmentSpecifier
	 */
	default void on(final IASTAlignmentSpecifier alignmentSpecifier) {
		on((IASTNode) alignmentSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclarator)}.
	 *
	 * @param arrayDeclarator
	 *            arrayDeclarator
	 */
	default void on(final IASTArrayDeclarator arrayDeclarator) {
		on((IASTDeclarator) arrayDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(ICASTArrayModifier)}
	 *
	 * IASTArrayModifier.getPropertyInParent() values
	 *   {@link IASTArrayDeclarator#ARRAY_MODIFIER}
	 * </pre>
	 *
	 * @param arrayModifier
	 *            arrayModifier
	 */
	default void on(final IASTArrayModifier arrayModifier) {
		on((IASTNode) arrayModifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param arraySubscriptExpression
	 *            arraySubscriptExpression
	 */
	default void on(final IASTArraySubscriptExpression arraySubscriptExpression) {
		on((IASTExpression) arraySubscriptExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclaration)}.
	 *
	 * @param asmDeclaration
	 *            asmDeclaration
	 */
	default void on(final IASTASMDeclaration asmDeclaration) {
		on((IASTDeclaration) asmDeclaration);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTAttribute.getPropertyInParent() values
	 *   {@link IASTAttributeSpecifier#ATTRIBUTE}
	 * </pre>
	 *
	 * @param attribute
	 *            attribute
	 */
	default void on(final IASTAttribute attribute) {
		on((IASTNode) attribute);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(IGCCASTAttributeSpecifier)}
	 *
	 * IASTAttributeSpecifier.getPropertyInParent() values
	 *   {@link IASTAttributeOwner#ATTRIBUTE_SPECIFIER}
	 * </pre>
	 *
	 * @param attributeSpecifier
	 *            attributeSpecifier
	 */
	default void on(final IASTAttributeSpecifier attributeSpecifier) {
		on((IASTNode) attributeSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param binaryExpression
	 *            binaryExpression
	 */
	default void on(final IASTBinaryExpression binaryExpression) {
		on((IASTExpression) binaryExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param binaryTypeIdExpression
	 *            binaryTypeIdExpression
	 */
	default void on(final IASTBinaryTypeIdExpression binaryTypeIdExpression) {
		on((IASTExpression) binaryTypeIdExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param breakStatement
	 *            breakStatement
	 */
	default void on(final IASTBreakStatement breakStatement) {
		on((IASTStatement) breakStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param caseStatement
	 *            caseStatement
	 */
	default void on(final IASTCaseStatement caseStatement) {
		on((IASTStatement) caseStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param castExpression
	 *            castExpression
	 */
	default void on(final IASTCastExpression castExpression) {
		on((IASTExpression) castExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTComment.getPropertyInParent() values
	 *   {@link IASTTranslationUnit#PREPROCESSOR_STATEMENT}
	 * </pre>
	 *
	 * @param comment
	 *            comment
	 */
	default void on(final IASTComment comment) {
		on((IASTNode) comment);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}.
	 *
	 * @param compositeTypeSpecifier
	 *            compositeTypeSpecifier
	 */
	default void on(final IASTCompositeTypeSpecifier compositeTypeSpecifier) {
		on((IASTDeclSpecifier) compositeTypeSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * <pre>
	 * IASTCompoundStatement.getPropertyInParent() values
	 *   {@link IGNUASTCompoundStatementExpression#STATEMENT}
	 * </pre>
	 *
	 * @param compoundStatement
	 *            compoundStatement
	 */
	default void on(final IASTCompoundStatement compoundStatement) {
		on((IASTStatement) compoundStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param conditionalExpression
	 *            conditionalExpression
	 */
	default void on(final IASTConditionalExpression conditionalExpression) {
		on((IASTExpression) conditionalExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param continueStatement
	 *            continueStatement
	 */
	default void on(final IASTContinueStatement continueStatement) {
		on((IASTStatement) continueStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
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
	 * </pre>
	 *
	 * @param declaration
	 *            declaration
	 */
	default void on(final IASTDeclaration declaration) {
		on((IASTNode) declaration);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param declarationStatement
	 *            declarationStatement
	 */
	default void on(final IASTDeclarationStatement declarationStatement) {
		on((IASTStatement) declarationStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
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
	 * </pre>
	 *
	 * @param declarator
	 *            declarator
	 */
	default void on(final IASTDeclarator declarator) {
		on((IASTNode) declarator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
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
	 * </pre>
	 *
	 * @param declSpecifier
	 *            declSpecifier
	 */
	default void on(final IASTDeclSpecifier declSpecifier) {
		on((IASTNode) declSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param defaultStatement
	 *            defaultStatement
	 */
	default void on(final IASTDefaultStatement defaultStatement) {
		on((IASTStatement) defaultStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param doStatement
	 *            doStatement
	 */
	default void on(final IASTDoStatement doStatement) {
		on((IASTStatement) doStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}.
	 *
	 * @param elaboratedTypeSpecifier
	 *            elaboratedTypeSpecifier
	 */
	default void on(final IASTElaboratedTypeSpecifier elaboratedTypeSpecifier) {
		on((IASTDeclSpecifier) elaboratedTypeSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}.
	 *
	 * @param enumerationSpecifier
	 *            enumerationSpecifier
	 */
	default void on(final IASTEnumerationSpecifier enumerationSpecifier) {
		on((IASTDeclSpecifier) enumerationSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTEnumerator.getPropertyInParent() values
	 *   {@link IASTEnumerationSpecifier#ENUMERATOR}
	 * </pre>
	 *
	 * @param enumerator
	 *            enumerator
	 */
	default void on(final IASTEnumerator enumerator) {
		on((IASTNode) enumerator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTInitializer)}.
	 *
	 * @param equalsInitializer
	 *            equalsInitializer
	 */
	default void on(final IASTEqualsInitializer equalsInitializer) {
		on((IASTInitializer) equalsInitializer);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
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
	 * </pre>
	 *
	 * @param expression
	 *            expression
	 */
	default void on(final IASTExpression expression) {
		on((IASTNode) expression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param expressionList
	 *            expressionList
	 */
	default void on(final IASTExpressionList expressionList) {
		on((IASTExpression) expressionList);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param expressionStatement
	 *            expressionStatement
	 */
	default void on(final IASTExpressionStatement expressionStatement) {
		on((IASTStatement) expressionStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclarator)}.
	 *
	 * @param fieldDeclarator
	 *            fieldDeclarator
	 */
	default void on(final IASTFieldDeclarator fieldDeclarator) {
		on((IASTDeclarator) fieldDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param fieldReference
	 *            fieldReference
	 */
	default void on(final IASTFieldReference fieldReference) {
		on((IASTExpression) fieldReference);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param forStatement
	 *            forStatement
	 */
	default void on(final IASTForStatement forStatement) {
		on((IASTStatement) forStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param functionCallExpression
	 *            functionCallExpression
	 */
	default void on(final IASTFunctionCallExpression functionCallExpression) {
		on((IASTExpression) functionCallExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclarator)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(IASTStandardFunctionDeclarator)}
	 *   {@link ASTNodeConsumer#on(ICASTKnRFunctionDeclarator)}
	 *
	 * IASTFunctionDeclarator.getPropertyInParent() values
	 *   {@link IASTFunctionDefinition#DECLARATOR}
	 * </pre>
	 *
	 * @param functionDeclarator
	 *            functionDeclarator
	 */
	default void on(final IASTFunctionDeclarator functionDeclarator) {
		on((IASTDeclarator) functionDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclaration)}.
	 *
	 * @param functionDefinition
	 *            functionDefinition
	 */
	default void on(final IASTFunctionDefinition functionDefinition) {
		on((IASTDeclaration) functionDefinition);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param gotoStatement
	 *            gotoStatement
	 */
	default void on(final IASTGotoStatement gotoStatement) {
		on((IASTStatement) gotoStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param idExpression
	 *            idExpression
	 */
	default void on(final IASTIdExpression idExpression) {
		on((IASTExpression) idExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param ifStatement
	 *            ifStatement
	 */
	default void on(final IASTIfStatement ifStatement) {
		on((IASTStatement) ifStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTImplicitName)}.
	 *
	 * <pre>
	 * IASTImplicitDestructorName.getPropertyInParent() values
	 *   {@link IASTImplicitDestructorNameOwner#IMPLICIT_DESTRUCTOR_NAME}
	 * </pre>
	 *
	 * @param implicitDestructorName
	 *            implicitDestructorName
	 */
	default void on(final IASTImplicitDestructorName implicitDestructorName) {
		on((IASTImplicitName) implicitDestructorName);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTName)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(IASTImplicitDestructorName)}
	 *
	 * IASTImplicitName.getPropertyInParent() values
	 *   {@link IASTImplicitNameOwner#IMPLICIT_NAME}
	 * </pre>
	 *
	 * @param implicitName
	 *            implicitName
	 */
	default void on(final IASTImplicitName implicitName) {
		on((IASTName) implicitName);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(IASTEqualsInitializer)}
	 *   {@link ASTNodeConsumer#on(IASTInitializerList)}
	 *   {@link ASTNodeConsumer#on(ICASTDesignatedInitializer)}
	 *
	 * IASTInitializer.getPropertyInParent() values
	 *   {@link IASTDeclarator#INITIALIZER}
	 *   {@link IASTTypeIdInitializerExpression#INITIALIZER}
	 * </pre>
	 *
	 * @param initializer
	 *            initializer
	 */
	default void on(final IASTInitializer initializer) {
		on((IASTNode) initializer);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTInitializer)}.
	 *
	 * <pre>
	 * IASTInitializerList.getPropertyInParent() values
	 *   {@link IASTEqualsInitializer#INITIALIZER}
	 *   {@link IASTFunctionCallExpression#ARGUMENT}
	 *   {@link IASTInitializerList#NESTED_INITIALIZER}
	 *   {@link IASTReturnStatement#RETURNVALUE}
	 *   {@link ICASTDesignatedInitializer#OPERAND}
	 * </pre>
	 *
	 * @param initializerList
	 *            initializerList
	 */
	default void on(final IASTInitializerList initializerList) {
		on((IASTInitializer) initializerList);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param labelStatement
	 *            labelStatement
	 */
	default void on(final IASTLabelStatement labelStatement) {
		on((IASTStatement) labelStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param literalExpression
	 *            literalExpression
	 */
	default void on(final IASTLiteralExpression literalExpression) {
		on((IASTExpression) literalExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
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
	 * </pre>
	 *
	 * @param name
	 *            name
	 */
	default void on(final IASTName name) {
		on((IASTNode) name);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}.
	 *
	 * @param namedTypeSpecifier
	 *            namedTypeSpecifier
	 */
	default void on(final IASTNamedTypeSpecifier namedTypeSpecifier) {
		on((IASTDeclSpecifier) namedTypeSpecifier);
	}
	
	/**
	 * Default overload if no override for the runtime type of node is implemented.
	 * 
	 * @param node
	 *            node
	 */
	void on(IASTNode node);
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param nullStatement
	 *            nullStatement
	 */
	default void on(final IASTNullStatement nullStatement) {
		on((IASTStatement) nullStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTParameterDeclaration.getPropertyInParent() values
	 *   {@link IASTStandardFunctionDeclarator#FUNCTION_PARAMETER}
	 * </pre>
	 *
	 * @param parameterDeclaration
	 *            parameterDeclaration
	 */
	default void on(final IASTParameterDeclaration parameterDeclaration) {
		on((IASTNode) parameterDeclaration);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPointerOperator)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(ICASTPointer)}
	 * </pre>
	 *
	 * @param pointer
	 *            pointer
	 */
	default void on(final IASTPointer pointer) {
		on((IASTPointerOperator) pointer);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(IASTPointer)}
	 *
	 * IASTPointerOperator.getPropertyInParent() values
	 *   {@link IASTDeclarator#POINTER_OPERATOR}
	 * </pre>
	 *
	 * @param pointerOperator
	 *            pointerOperator
	 */
	default void on(final IASTPointerOperator pointerOperator) {
		on((IASTNode) pointerOperator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorElifStatement
	 *            preprocessorElifStatement
	 */
	default void on(final IASTPreprocessorElifStatement preprocessorElifStatement) {
		on((IASTPreprocessorStatement) preprocessorElifStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorElseStatement
	 *            preprocessorElseStatement
	 */
	default void on(final IASTPreprocessorElseStatement preprocessorElseStatement) {
		on((IASTPreprocessorStatement) preprocessorElseStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorEndifStatement
	 *            preprocessorEndifStatement
	 */
	default void on(final IASTPreprocessorEndifStatement preprocessorEndifStatement) {
		on((IASTPreprocessorStatement) preprocessorEndifStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorErrorStatement
	 *            preprocessorErrorStatement
	 */
	default void on(final IASTPreprocessorErrorStatement preprocessorErrorStatement) {
		on((IASTPreprocessorStatement) preprocessorErrorStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorMacroDefinition)}.
	 *
	 * @param preprocessorFunctionStyleMacroDefinition
	 *            preprocessorFunctionStyleMacroDefinition
	 */
	default void on(final IASTPreprocessorFunctionStyleMacroDefinition preprocessorFunctionStyleMacroDefinition) {
		on((IASTPreprocessorMacroDefinition) preprocessorFunctionStyleMacroDefinition);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorIfdefStatement
	 *            preprocessorIfdefStatement
	 */
	default void on(final IASTPreprocessorIfdefStatement preprocessorIfdefStatement) {
		on((IASTPreprocessorStatement) preprocessorIfdefStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorIfndefStatement
	 *            preprocessorIfndefStatement
	 */
	default void on(final IASTPreprocessorIfndefStatement preprocessorIfndefStatement) {
		on((IASTPreprocessorStatement) preprocessorIfndefStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorIfStatement
	 *            preprocessorIfStatement
	 */
	default void on(final IASTPreprocessorIfStatement preprocessorIfStatement) {
		on((IASTPreprocessorStatement) preprocessorIfStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorIncludeStatement
	 *            preprocessorIncludeStatement
	 */
	default void on(final IASTPreprocessorIncludeStatement preprocessorIncludeStatement) {
		on((IASTPreprocessorStatement) preprocessorIncludeStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorFunctionStyleMacroDefinition)}
	 *   {@link ASTNodeConsumer#on(IASTPreprocessorObjectStyleMacroDefinition)}
	 * </pre>
	 *
	 * @param preprocessorMacroDefinition
	 *            preprocessorMacroDefinition
	 */
	default void on(final IASTPreprocessorMacroDefinition preprocessorMacroDefinition) {
		on((IASTPreprocessorStatement) preprocessorMacroDefinition);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTPreprocessorMacroExpansion.getPropertyInParent() values
	 *   {@link IASTTranslationUnit#MACRO_EXPANSION}
	 * </pre>
	 *
	 * @param preprocessorMacroExpansion
	 *            preprocessorMacroExpansion
	 */
	default void on(final IASTPreprocessorMacroExpansion preprocessorMacroExpansion) {
		on((IASTNode) preprocessorMacroExpansion);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorMacroDefinition)}.
	 *
	 * @param preprocessorObjectStyleMacroDefinition
	 *            preprocessorObjectStyleMacroDefinition
	 */
	default void on(final IASTPreprocessorObjectStyleMacroDefinition preprocessorObjectStyleMacroDefinition) {
		on((IASTPreprocessorMacroDefinition) preprocessorObjectStyleMacroDefinition);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorPragmaStatement
	 *            preprocessorPragmaStatement
	 */
	default void on(final IASTPreprocessorPragmaStatement preprocessorPragmaStatement) {
		on((IASTPreprocessorStatement) preprocessorPragmaStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
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
	 * </pre>
	 *
	 * @param preprocessorStatement
	 *            preprocessorStatement
	 */
	default void on(final IASTPreprocessorStatement preprocessorStatement) {
		on((IASTNode) preprocessorStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorUndefStatement
	 *            preprocessorUndefStatement
	 */
	default void on(final IASTPreprocessorUndefStatement preprocessorUndefStatement) {
		on((IASTPreprocessorStatement) preprocessorUndefStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTProblem.getPropertyInParent() values
	 *   {@link IASTTranslationUnit#SCANNER_PROBLEM}
	 * </pre>
	 *
	 * @param problem
	 *            problem
	 */
	default void on(final IASTProblem problem) {
		on((IASTNode) problem);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclaration)}.
	 *
	 * @param problemDeclaration
	 *            problemDeclaration
	 */
	default void on(final IASTProblemDeclaration problemDeclaration) {
		on((IASTDeclaration) problemDeclaration);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param problemExpression
	 *            problemExpression
	 */
	default void on(final IASTProblemExpression problemExpression) {
		on((IASTExpression) problemExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param problemStatement
	 *            problemStatement
	 */
	default void on(final IASTProblemStatement problemStatement) {
		on((IASTStatement) problemStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTTypeId)}.
	 *
	 * @param problemTypeId
	 *            problemTypeId
	 */
	default void on(final IASTProblemTypeId problemTypeId) {
		on((IASTTypeId) problemTypeId);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param returnStatement
	 *            returnStatement
	 */
	default void on(final IASTReturnStatement returnStatement) {
		on((IASTStatement) returnStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclaration)}.
	 *
	 * @param simpleDeclaration
	 *            simpleDeclaration
	 */
	default void on(final IASTSimpleDeclaration simpleDeclaration) {
		on((IASTDeclaration) simpleDeclaration);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTDeclSpecifier)}.
	 *
	 * @param simpleDeclSpecifier
	 *            simpleDeclSpecifier
	 */
	default void on(final IASTSimpleDeclSpecifier simpleDeclSpecifier) {
		on((IASTDeclSpecifier) simpleDeclSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTFunctionDeclarator)}.
	 *
	 * @param standardFunctionDeclarator
	 *            standardFunctionDeclarator
	 */
	default void on(final IASTStandardFunctionDeclarator standardFunctionDeclarator) {
		on((IASTFunctionDeclarator) standardFunctionDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
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
	 * </pre>
	 *
	 * @param statement
	 *            statement
	 */
	default void on(final IASTStatement statement) {
		on((IASTNode) statement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param switchStatement
	 *            switchStatement
	 */
	default void on(final IASTSwitchStatement switchStatement) {
		on((IASTStatement) switchStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(IASTTokenList)}
	 *
	 * IASTToken.getPropertyInParent() values
	 *   {@link IASTAttribute#ARGUMENT_CLAUSE}
	 *   {@link IASTTokenList#NESTED_TOKEN}
	 * </pre>
	 *
	 * @param token
	 *            token
	 */
	default void on(final IASTToken token) {
		on((IASTNode) token);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTToken)}.
	 *
	 * @param tokenList
	 *            tokenList
	 */
	default void on(final IASTTokenList tokenList) {
		on((IASTToken) tokenList);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * @param translationUnit
	 *            translationUnit
	 */
	default void on(final IASTTranslationUnit translationUnit) {
		on((IASTNode) translationUnit);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
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
	 * </pre>
	 *
	 * @param typeId
	 *            typeId
	 */
	default void on(final IASTTypeId typeId) {
		on((IASTNode) typeId);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param typeIdExpression
	 *            typeIdExpression
	 */
	default void on(final IASTTypeIdExpression typeIdExpression) {
		on((IASTExpression) typeIdExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param typeIdInitializerExpression
	 *            typeIdInitializerExpression
	 */
	default void on(final IASTTypeIdInitializerExpression typeIdInitializerExpression) {
		on((IASTExpression) typeIdInitializerExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param unaryExpression
	 *            unaryExpression
	 */
	default void on(final IASTUnaryExpression unaryExpression) {
		on((IASTExpression) unaryExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param whileStatement
	 *            whileStatement
	 */
	default void on(final IASTWhileStatement whileStatement) {
		on((IASTStatement) whileStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(ICASTDesignator)}.
	 *
	 * @param castArrayDesignator
	 *            cArrayDesignator
	 */
	default void on(final ICASTArrayDesignator castArrayDesignator) {
		on((ICASTDesignator) castArrayDesignator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTArrayModifier)}.
	 *
	 * @param castArrayModifier
	 *            cArrayModifier
	 */
	default void on(final ICASTArrayModifier castArrayModifier) {
		on((IASTArrayModifier) castArrayModifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTInitializer)}.
	 *
	 * <pre>
	 * ICASTDesignatedInitializer.getPropertyInParent() values
	 *   {@link IASTEqualsInitializer#INITIALIZER}
	 *   {@link IASTFunctionCallExpression#ARGUMENT}
	 *   {@link IASTInitializerList#NESTED_INITIALIZER}
	 *   {@link IASTReturnStatement#RETURNVALUE}
	 *   {@link ICASTDesignatedInitializer#OPERAND}
	 * </pre>
	 *
	 * @param castDesignatedInitializer
	 *            cDesignatedInitializer
	 */
	default void on(final ICASTDesignatedInitializer castDesignatedInitializer) {
		on((IASTInitializer) castDesignatedInitializer);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeConsumer#on(ICASTArrayDesignator)}
	 *   {@link ASTNodeConsumer#on(ICASTFieldDesignator)}
	 *   {@link ASTNodeConsumer#on(IGCCASTArrayRangeDesignator)}
	 *
	 * ICASTDesignator.getPropertyInParent() values
	 *   {@link ICASTDesignatedInitializer#DESIGNATOR}
	 * </pre>
	 *
	 * @param castDesignator
	 *            cDesignator
	 */
	default void on(final ICASTDesignator castDesignator) {
		on((IASTNode) castDesignator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(ICASTDesignator)}.
	 *
	 * @param castFieldDesignator
	 *            cFieldDesignator
	 */
	default void on(final ICASTFieldDesignator castFieldDesignator) {
		on((ICASTDesignator) castFieldDesignator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTFunctionDeclarator)}.
	 *
	 * @param castKnRFunctionDeclarator
	 *            cKnRFunctionDeclarator
	 */
	default void on(final ICASTKnRFunctionDeclarator castKnRFunctionDeclarator) {
		on((IASTFunctionDeclarator) castKnRFunctionDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTPointer)}.
	 *
	 * @param castPointer
	 *            cPointer
	 */
	default void on(final ICASTPointer castPointer) {
		on((IASTPointer) castPointer);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(ICASTDesignator)}.
	 *
	 * @param gccArrayRangeDesignator
	 *            gccArrayRangeDesignator
	 */
	default void on(final IGCCASTArrayRangeDesignator gccArrayRangeDesignator) {
		on((ICASTDesignator) gccArrayRangeDesignator);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTAttributeSpecifier)}.
	 *
	 * @param gccAttributeSpecifier
	 *            gccAttributeSpecifier
	 */
	default void on(final IGCCASTAttributeSpecifier gccAttributeSpecifier) {
		on((IASTAttributeSpecifier) gccAttributeSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTExpression)}.
	 *
	 * @param gnuCompoundStatementExpression
	 *            gnuCompoundStatementExpression
	 */
	default void on(final IGNUASTCompoundStatementExpression gnuCompoundStatementExpression) {
		on((IASTExpression) gnuCompoundStatementExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTStatement)}.
	 *
	 * @param gnuGotoStatement
	 *            gnuGotoStatement
	 */
	default void on(final IGNUASTGotoStatement gnuGotoStatement) {
		on((IASTStatement) gnuGotoStatement);
	}
}
