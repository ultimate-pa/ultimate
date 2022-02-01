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
 * 
 * @param <T>
 *            returned type
 */
@FunctionalInterface
public interface IASTNodeFunction<T> {
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTAlignmentSpecifier.getPropertyInParent() values
	 *   {@link IASTDeclSpecifier#ALIGNMENT_SPECIFIER}
	 * </pre>
	 * 
	 * @param alignmentSpecifier
	 *            alignmentSpecifier
	 * @return return value for nodes of type IASTAlignmentSpecifier
	 */
	default T on(final IASTAlignmentSpecifier alignmentSpecifier) {
		return on((IASTNode) alignmentSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclarator)}.
	 *
	 * @param arrayDeclarator
	 *            arrayDeclarator
	 * @return return value for nodes of type IASTArrayDeclarator
	 */
	default T on(final IASTArrayDeclarator arrayDeclarator) {
		return on((IASTDeclarator) arrayDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(ICASTArrayModifier)}
	 *
	 * IASTArrayModifier.getPropertyInParent() values
	 *   {@link IASTArrayDeclarator#ARRAY_MODIFIER}
	 * </pre>
	 * 
	 * @param arrayModifier
	 *            arrayModifier
	 * @return return value for nodes of type IASTArrayModifier
	 */
	default T on(final IASTArrayModifier arrayModifier) {
		return on((IASTNode) arrayModifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param arraySubscriptExpression
	 *            arraySubscriptExpression
	 * @return return value for nodes of type IASTArraySubscriptExpression
	 */
	default T on(final IASTArraySubscriptExpression arraySubscriptExpression) {
		return on((IASTExpression) arraySubscriptExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclaration)}.
	 *
	 * @param asmDeclaration
	 *            asmDeclaration
	 * @return return value for nodes of type IASTASMDeclaration
	 */
	default T on(final IASTASMDeclaration asmDeclaration) {
		return on((IASTDeclaration) asmDeclaration);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTAttribute.getPropertyInParent() values
	 *   {@link IASTAttributeSpecifier#ATTRIBUTE}
	 * </pre>
	 * 
	 * @param attribute
	 *            attribute
	 * @return return value for nodes of type IASTAttribute
	 */
	default T on(final IASTAttribute attribute) {
		return on((IASTNode) attribute);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IGCCASTAttributeSpecifier)}
	 *
	 * IASTAttributeSpecifier.getPropertyInParent() values
	 *   {@link IASTAttributeOwner#ATTRIBUTE_SPECIFIER}
	 * </pre>
	 * 
	 * @param attributeSpecifier
	 *            attributeSpecifier
	 * @return return value for nodes of type IASTAttributeSpecifier
	 */
	default T on(final IASTAttributeSpecifier attributeSpecifier) {
		return on((IASTNode) attributeSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param binaryExpression
	 *            binaryExpression
	 * @return return value for nodes of type IASTBinaryExpression
	 */
	default T on(final IASTBinaryExpression binaryExpression) {
		return on((IASTExpression) binaryExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param binaryTypeIdExpression
	 *            binaryTypeIdExpression
	 * @return return value for nodes of type IASTBinaryTypeIdExpression
	 */
	default T on(final IASTBinaryTypeIdExpression binaryTypeIdExpression) {
		return on((IASTExpression) binaryTypeIdExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param breakStatement
	 *            breakStatement
	 * @return return value for nodes of type IASTBreakStatement
	 */
	default T on(final IASTBreakStatement breakStatement) {
		return on((IASTStatement) breakStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param caseStatement
	 *            caseStatement
	 * @return return value for nodes of type IASTCaseStatement
	 */
	default T on(final IASTCaseStatement caseStatement) {
		return on((IASTStatement) caseStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param castExpression
	 *            castExpression
	 * @return return value for nodes of type IASTCastExpression
	 */
	default T on(final IASTCastExpression castExpression) {
		return on((IASTExpression) castExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTComment.getPropertyInParent() values
	 *   {@link IASTTranslationUnit#PREPROCESSOR_STATEMENT}
	 * </pre>
	 * 
	 * @param comment
	 *            comment
	 * @return return value for nodes of type IASTComment
	 */
	default T on(final IASTComment comment) {
		return on((IASTNode) comment);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclSpecifier)}.
	 *
	 * @param compositeTypeSpecifier
	 *            compositeTypeSpecifier
	 * @return return value for nodes of type IASTCompositeTypeSpecifier
	 */
	default T on(final IASTCompositeTypeSpecifier compositeTypeSpecifier) {
		return on((IASTDeclSpecifier) compositeTypeSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * <pre>
	 * IASTCompoundStatement.getPropertyInParent() values
	 *   {@link IGNUASTCompoundStatementExpression#STATEMENT}
	 * </pre>
	 * 
	 * @param compoundStatement
	 *            compoundStatement
	 * @return return value for nodes of type IASTCompoundStatement
	 */
	default T on(final IASTCompoundStatement compoundStatement) {
		return on((IASTStatement) compoundStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param conditionalExpression
	 *            conditionalExpression
	 * @return return value for nodes of type IASTConditionalExpression
	 */
	default T on(final IASTConditionalExpression conditionalExpression) {
		return on((IASTExpression) conditionalExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param continueStatement
	 *            continueStatement
	 * @return return value for nodes of type IASTContinueStatement
	 */
	default T on(final IASTContinueStatement continueStatement) {
		return on((IASTStatement) continueStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTASMDeclaration)}
	 *   {@link ASTNodeFunction#on(IASTFunctionDefinition)}
	 *   {@link ASTNodeFunction#on(IASTProblemDeclaration)}
	 *   {@link ASTNodeFunction#on(IASTSimpleDeclaration)}
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
	 * @return return value for nodes of type IASTDeclaration
	 */
	default T on(final IASTDeclaration declaration) {
		return on((IASTNode) declaration);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param declarationStatement
	 *            declarationStatement
	 * @return return value for nodes of type IASTDeclarationStatement
	 */
	default T on(final IASTDeclarationStatement declarationStatement) {
		return on((IASTStatement) declarationStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTArrayDeclarator)}
	 *   {@link ASTNodeFunction#on(IASTFieldDeclarator)}
	 *   {@link ASTNodeFunction#on(IASTFunctionDeclarator)}
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
	 * @return return value for nodes of type IASTDeclarator
	 */
	default T on(final IASTDeclarator declarator) {
		return on((IASTNode) declarator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTCompositeTypeSpecifier)}
	 *   {@link ASTNodeFunction#on(IASTElaboratedTypeSpecifier)}
	 *   {@link ASTNodeFunction#on(IASTEnumerationSpecifier)}
	 *   {@link ASTNodeFunction#on(IASTNamedTypeSpecifier)}
	 *   {@link ASTNodeFunction#on(IASTSimpleDeclSpecifier)}
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
	 * @return return value for nodes of type IASTDeclSpecifier
	 */
	default T on(final IASTDeclSpecifier declSpecifier) {
		return on((IASTNode) declSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param defaultStatement
	 *            defaultStatement
	 * @return return value for nodes of type IASTDefaultStatement
	 */
	default T on(final IASTDefaultStatement defaultStatement) {
		return on((IASTStatement) defaultStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param doStatement
	 *            doStatement
	 * @return return value for nodes of type IASTDoStatement
	 */
	default T on(final IASTDoStatement doStatement) {
		return on((IASTStatement) doStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclSpecifier)}.
	 *
	 * @param elaboratedTypeSpecifier
	 *            elaboratedTypeSpecifier
	 * @return return value for nodes of type IASTElaboratedTypeSpecifier
	 */
	default T on(final IASTElaboratedTypeSpecifier elaboratedTypeSpecifier) {
		return on((IASTDeclSpecifier) elaboratedTypeSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclSpecifier)}.
	 *
	 * @param enumerationSpecifier
	 *            enumerationSpecifier
	 * @return return value for nodes of type IASTEnumerationSpecifier
	 */
	default T on(final IASTEnumerationSpecifier enumerationSpecifier) {
		return on((IASTDeclSpecifier) enumerationSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTEnumerator.getPropertyInParent() values
	 *   {@link IASTEnumerationSpecifier#ENUMERATOR}
	 * </pre>
	 * 
	 * @param enumerator
	 *            enumerator
	 * @return return value for nodes of type IASTEnumerator
	 */
	default T on(final IASTEnumerator enumerator) {
		return on((IASTNode) enumerator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTInitializer)}.
	 *
	 * @param equalsInitializer
	 *            equalsInitializer
	 * @return return value for nodes of type IASTEqualsInitializer
	 */
	default T on(final IASTEqualsInitializer equalsInitializer) {
		return on((IASTInitializer) equalsInitializer);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTArraySubscriptExpression)}
	 *   {@link ASTNodeFunction#on(IASTBinaryExpression)}
	 *   {@link ASTNodeFunction#on(IASTBinaryTypeIdExpression)}
	 *   {@link ASTNodeFunction#on(IASTCastExpression)}
	 *   {@link ASTNodeFunction#on(IASTConditionalExpression)}
	 *   {@link ASTNodeFunction#on(IASTExpressionList)}
	 *   {@link ASTNodeFunction#on(IASTFieldReference)}
	 *   {@link ASTNodeFunction#on(IASTFunctionCallExpression)}
	 *   {@link ASTNodeFunction#on(IASTIdExpression)}
	 *   {@link ASTNodeFunction#on(IASTLiteralExpression)}
	 *   {@link ASTNodeFunction#on(IASTProblemExpression)}
	 *   {@link ASTNodeFunction#on(IASTTypeIdExpression)}
	 *   {@link ASTNodeFunction#on(IASTTypeIdInitializerExpression)}
	 *   {@link ASTNodeFunction#on(IASTUnaryExpression)}
	 *   {@link ASTNodeFunction#on(IGNUASTCompoundStatementExpression)}
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
	 * @return return value for nodes of type IASTExpression
	 */
	default T on(final IASTExpression expression) {
		return on((IASTNode) expression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param expressionList
	 *            expressionList
	 * @return return value for nodes of type IASTExpressionList
	 */
	default T on(final IASTExpressionList expressionList) {
		return on((IASTExpression) expressionList);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param expressionStatement
	 *            expressionStatement
	 * @return return value for nodes of type IASTExpressionStatement
	 */
	default T on(final IASTExpressionStatement expressionStatement) {
		return on((IASTStatement) expressionStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclarator)}.
	 *
	 * @param fieldDeclarator
	 *            fieldDeclarator
	 * @return return value for nodes of type IASTFieldDeclarator
	 */
	default T on(final IASTFieldDeclarator fieldDeclarator) {
		return on((IASTDeclarator) fieldDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param fieldReference
	 *            fieldReference
	 * @return return value for nodes of type IASTFieldReference
	 */
	default T on(final IASTFieldReference fieldReference) {
		return on((IASTExpression) fieldReference);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param forStatement
	 *            forStatement
	 * @return return value for nodes of type IASTForStatement
	 */
	default T on(final IASTForStatement forStatement) {
		return on((IASTStatement) forStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param functionCallExpression
	 *            functionCallExpression
	 * @return return value for nodes of type IASTFunctionCallExpression
	 */
	default T on(final IASTFunctionCallExpression functionCallExpression) {
		return on((IASTExpression) functionCallExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclarator)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTStandardFunctionDeclarator)}
	 *   {@link ASTNodeFunction#on(ICASTKnRFunctionDeclarator)}
	 *
	 * IASTFunctionDeclarator.getPropertyInParent() values
	 *   {@link IASTFunctionDefinition#DECLARATOR}
	 * </pre>
	 * 
	 * @param functionDeclarator
	 *            functionDeclarator
	 * @return return value for nodes of type IASTFunctionDeclarator
	 */
	default T on(final IASTFunctionDeclarator functionDeclarator) {
		return on((IASTDeclarator) functionDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclaration)}.
	 *
	 * @param functionDefinition
	 *            functionDefinition
	 * @return return value for nodes of type IASTFunctionDefinition
	 */
	default T on(final IASTFunctionDefinition functionDefinition) {
		return on((IASTDeclaration) functionDefinition);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param gotoStatement
	 *            gotoStatement
	 * @return return value for nodes of type IASTGotoStatement
	 */
	default T on(final IASTGotoStatement gotoStatement) {
		return on((IASTStatement) gotoStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param idExpression
	 *            idExpression
	 * @return return value for nodes of type IASTIdExpression
	 */
	default T on(final IASTIdExpression idExpression) {
		return on((IASTExpression) idExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param ifStatement
	 *            ifStatement
	 * @return return value for nodes of type IASTIfStatement
	 */
	default T on(final IASTIfStatement ifStatement) {
		return on((IASTStatement) ifStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTImplicitName)}.
	 *
	 * <pre>
	 * IASTImplicitDestructorName.getPropertyInParent() values
	 *   {@link IASTImplicitDestructorNameOwner#IMPLICIT_DESTRUCTOR_NAME}
	 * </pre>
	 * 
	 * @param implicitDestructorName
	 *            implicitDestructorName
	 * @return return value for nodes of type IASTImplicitDestructorName
	 */
	default T on(final IASTImplicitDestructorName implicitDestructorName) {
		return on((IASTImplicitName) implicitDestructorName);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTName)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTImplicitDestructorName)}
	 *
	 * IASTImplicitName.getPropertyInParent() values
	 *   {@link IASTImplicitNameOwner#IMPLICIT_NAME}
	 * </pre>
	 * 
	 * @param implicitName
	 *            implicitName
	 * @return return value for nodes of type IASTImplicitName
	 */
	default T on(final IASTImplicitName implicitName) {
		return on((IASTName) implicitName);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTEqualsInitializer)}
	 *   {@link ASTNodeFunction#on(IASTInitializerList)}
	 *   {@link ASTNodeFunction#on(ICASTDesignatedInitializer)}
	 *
	 * IASTInitializer.getPropertyInParent() values
	 *   {@link IASTDeclarator#INITIALIZER}
	 *   {@link IASTTypeIdInitializerExpression#INITIALIZER}
	 * </pre>
	 * 
	 * @param initializer
	 *            initializer
	 * @return return value for nodes of type IASTInitializer
	 */
	default T on(final IASTInitializer initializer) {
		return on((IASTNode) initializer);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTInitializer)}.
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
	 * @return return value for nodes of type IASTInitializerList
	 */
	default T on(final IASTInitializerList initializerList) {
		return on((IASTInitializer) initializerList);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param labelStatement
	 *            labelStatement
	 * @return return value for nodes of type IASTLabelStatement
	 */
	default T on(final IASTLabelStatement labelStatement) {
		return on((IASTStatement) labelStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param literalExpression
	 *            literalExpression
	 * @return return value for nodes of type IASTLiteralExpression
	 */
	default T on(final IASTLiteralExpression literalExpression) {
		return on((IASTExpression) literalExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTImplicitName)}
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
	 * @return return value for nodes of type IASTName
	 */
	default T on(final IASTName name) {
		return on((IASTNode) name);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclSpecifier)}.
	 *
	 * @param namedTypeSpecifier
	 *            namedTypeSpecifier
	 * @return return value for nodes of type IASTNamedTypeSpecifier
	 */
	default T on(final IASTNamedTypeSpecifier namedTypeSpecifier) {
		return on((IASTDeclSpecifier) namedTypeSpecifier);
	}
	
	/**
	 * Default overload if no override for the runtime type of node is implemented.
	 * 
	 * @param node
	 *            node
	 * @return default return value
	 */
	T on(IASTNode node);
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param nullStatement
	 *            nullStatement
	 * @return return value for nodes of type IASTNullStatement
	 */
	default T on(final IASTNullStatement nullStatement) {
		return on((IASTStatement) nullStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTParameterDeclaration.getPropertyInParent() values
	 *   {@link IASTStandardFunctionDeclarator#FUNCTION_PARAMETER}
	 * </pre>
	 * 
	 * @param parameterDeclaration
	 *            parameterDeclaration
	 * @return return value for nodes of type IASTParameterDeclaration
	 */
	default T on(final IASTParameterDeclaration parameterDeclaration) {
		return on((IASTNode) parameterDeclaration);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPointerOperator)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(ICASTPointer)}
	 * </pre>
	 * 
	 * @param pointer
	 *            pointer
	 * @return return value for nodes of type IASTPointer
	 */
	default T on(final IASTPointer pointer) {
		return on((IASTPointerOperator) pointer);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTPointer)}
	 *
	 * IASTPointerOperator.getPropertyInParent() values
	 *   {@link IASTDeclarator#POINTER_OPERATOR}
	 * </pre>
	 * 
	 * @param pointerOperator
	 *            pointerOperator
	 * @return return value for nodes of type IASTPointerOperator
	 */
	default T on(final IASTPointerOperator pointerOperator) {
		return on((IASTNode) pointerOperator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorElifStatement
	 *            preprocessorElifStatement
	 * @return return value for nodes of type IASTPreprocessorElifStatement
	 */
	default T on(final IASTPreprocessorElifStatement preprocessorElifStatement) {
		return on((IASTPreprocessorStatement) preprocessorElifStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorElseStatement
	 *            preprocessorElseStatement
	 * @return return value for nodes of type IASTPreprocessorElseStatement
	 */
	default T on(final IASTPreprocessorElseStatement preprocessorElseStatement) {
		return on((IASTPreprocessorStatement) preprocessorElseStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorEndifStatement
	 *            preprocessorEndifStatement
	 * @return return value for nodes of type IASTPreprocessorEndifStatement
	 */
	default T on(final IASTPreprocessorEndifStatement preprocessorEndifStatement) {
		return on((IASTPreprocessorStatement) preprocessorEndifStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorErrorStatement
	 *            preprocessorErrorStatement
	 * @return return value for nodes of type IASTPreprocessorErrorStatement
	 */
	default T on(final IASTPreprocessorErrorStatement preprocessorErrorStatement) {
		return on((IASTPreprocessorStatement) preprocessorErrorStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorMacroDefinition)}.
	 *
	 * @param preprocessorFunctionStyleMacroDefinition
	 *            preprocessorFunctionStyleMacroDefinition
	 * @return return value for nodes of type IASTPreprocessorFunctionStyleMacroDefinition
	 */
	default T on(final IASTPreprocessorFunctionStyleMacroDefinition preprocessorFunctionStyleMacroDefinition) {
		return on((IASTPreprocessorMacroDefinition) preprocessorFunctionStyleMacroDefinition);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorIfdefStatement
	 *            preprocessorIfdefStatement
	 * @return return value for nodes of type IASTPreprocessorIfdefStatement
	 */
	default T on(final IASTPreprocessorIfdefStatement preprocessorIfdefStatement) {
		return on((IASTPreprocessorStatement) preprocessorIfdefStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorIfndefStatement
	 *            preprocessorIfndefStatement
	 * @return return value for nodes of type IASTPreprocessorIfndefStatement
	 */
	default T on(final IASTPreprocessorIfndefStatement preprocessorIfndefStatement) {
		return on((IASTPreprocessorStatement) preprocessorIfndefStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorIfStatement
	 *            preprocessorIfStatement
	 * @return return value for nodes of type IASTPreprocessorIfStatement
	 */
	default T on(final IASTPreprocessorIfStatement preprocessorIfStatement) {
		return on((IASTPreprocessorStatement) preprocessorIfStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorIncludeStatement
	 *            preprocessorIncludeStatement
	 * @return return value for nodes of type IASTPreprocessorIncludeStatement
	 */
	default T on(final IASTPreprocessorIncludeStatement preprocessorIncludeStatement) {
		return on((IASTPreprocessorStatement) preprocessorIncludeStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTPreprocessorFunctionStyleMacroDefinition)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorObjectStyleMacroDefinition)}
	 * </pre>
	 * 
	 * @param preprocessorMacroDefinition
	 *            preprocessorMacroDefinition
	 * @return return value for nodes of type IASTPreprocessorMacroDefinition
	 */
	default T on(final IASTPreprocessorMacroDefinition preprocessorMacroDefinition) {
		return on((IASTPreprocessorStatement) preprocessorMacroDefinition);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTPreprocessorMacroExpansion.getPropertyInParent() values
	 *   {@link IASTTranslationUnit#MACRO_EXPANSION}
	 * </pre>
	 * 
	 * @param preprocessorMacroExpansion
	 *            preprocessorMacroExpansion
	 * @return return value for nodes of type IASTPreprocessorMacroExpansion
	 */
	default T on(final IASTPreprocessorMacroExpansion preprocessorMacroExpansion) {
		return on((IASTNode) preprocessorMacroExpansion);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorMacroDefinition)}.
	 *
	 * @param preprocessorObjectStyleMacroDefinition
	 *            preprocessorObjectStyleMacroDefinition
	 * @return return value for nodes of type IASTPreprocessorObjectStyleMacroDefinition
	 */
	default T on(final IASTPreprocessorObjectStyleMacroDefinition preprocessorObjectStyleMacroDefinition) {
		return on((IASTPreprocessorMacroDefinition) preprocessorObjectStyleMacroDefinition);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorPragmaStatement
	 *            preprocessorPragmaStatement
	 * @return return value for nodes of type IASTPreprocessorPragmaStatement
	 */
	default T on(final IASTPreprocessorPragmaStatement preprocessorPragmaStatement) {
		return on((IASTPreprocessorStatement) preprocessorPragmaStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTPreprocessorElifStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorElseStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorEndifStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorErrorStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorIfStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorIfdefStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorIfndefStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorIncludeStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorMacroDefinition)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorPragmaStatement)}
	 *   {@link ASTNodeFunction#on(IASTPreprocessorUndefStatement)}
	 *
	 * IASTPreprocessorStatement.getPropertyInParent() values
	 *   {@link IASTTranslationUnit#PREPROCESSOR_STATEMENT}
	 * </pre>
	 * 
	 * @param preprocessorStatement
	 *            preprocessorStatement
	 * @return return value for nodes of type IASTPreprocessorStatement
	 */
	default T on(final IASTPreprocessorStatement preprocessorStatement) {
		return on((IASTNode) preprocessorStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPreprocessorStatement)}.
	 *
	 * @param preprocessorUndefStatement
	 *            preprocessorUndefStatement
	 * @return return value for nodes of type IASTPreprocessorUndefStatement
	 */
	default T on(final IASTPreprocessorUndefStatement preprocessorUndefStatement) {
		return on((IASTPreprocessorStatement) preprocessorUndefStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * IASTProblem.getPropertyInParent() values
	 *   {@link IASTTranslationUnit#SCANNER_PROBLEM}
	 * </pre>
	 * 
	 * @param problem
	 *            problem
	 * @return return value for nodes of type IASTProblem
	 */
	default T on(final IASTProblem problem) {
		return on((IASTNode) problem);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclaration)}.
	 *
	 * @param problemDeclaration
	 *            problemDeclaration
	 * @return return value for nodes of type IASTProblemDeclaration
	 */
	default T on(final IASTProblemDeclaration problemDeclaration) {
		return on((IASTDeclaration) problemDeclaration);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param problemExpression
	 *            problemExpression
	 * @return return value for nodes of type IASTProblemExpression
	 */
	default T on(final IASTProblemExpression problemExpression) {
		return on((IASTExpression) problemExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param problemStatement
	 *            problemStatement
	 * @return return value for nodes of type IASTProblemStatement
	 */
	default T on(final IASTProblemStatement problemStatement) {
		return on((IASTStatement) problemStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTTypeId)}.
	 *
	 * @param problemTypeId
	 *            problemTypeId
	 * @return return value for nodes of type IASTProblemTypeId
	 */
	default T on(final IASTProblemTypeId problemTypeId) {
		return on((IASTTypeId) problemTypeId);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param returnStatement
	 *            returnStatement
	 * @return return value for nodes of type IASTReturnStatement
	 */
	default T on(final IASTReturnStatement returnStatement) {
		return on((IASTStatement) returnStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclaration)}.
	 *
	 * @param simpleDeclaration
	 *            simpleDeclaration
	 * @return return value for nodes of type IASTSimpleDeclaration
	 */
	default T on(final IASTSimpleDeclaration simpleDeclaration) {
		return on((IASTDeclaration) simpleDeclaration);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTDeclSpecifier)}.
	 *
	 * @param simpleDeclSpecifier
	 *            simpleDeclSpecifier
	 * @return return value for nodes of type IASTSimpleDeclSpecifier
	 */
	default T on(final IASTSimpleDeclSpecifier simpleDeclSpecifier) {
		return on((IASTDeclSpecifier) simpleDeclSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTFunctionDeclarator)}.
	 *
	 * @param standardFunctionDeclarator
	 *            standardFunctionDeclarator
	 * @return return value for nodes of type IASTStandardFunctionDeclarator
	 */
	default T on(final IASTStandardFunctionDeclarator standardFunctionDeclarator) {
		return on((IASTFunctionDeclarator) standardFunctionDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTBreakStatement)}
	 *   {@link ASTNodeFunction#on(IASTCaseStatement)}
	 *   {@link ASTNodeFunction#on(IASTCompoundStatement)}
	 *   {@link ASTNodeFunction#on(IASTContinueStatement)}
	 *   {@link ASTNodeFunction#on(IASTDeclarationStatement)}
	 *   {@link ASTNodeFunction#on(IASTDefaultStatement)}
	 *   {@link ASTNodeFunction#on(IASTDoStatement)}
	 *   {@link ASTNodeFunction#on(IASTExpressionStatement)}
	 *   {@link ASTNodeFunction#on(IASTForStatement)}
	 *   {@link ASTNodeFunction#on(IASTGotoStatement)}
	 *   {@link ASTNodeFunction#on(IASTIfStatement)}
	 *   {@link ASTNodeFunction#on(IASTLabelStatement)}
	 *   {@link ASTNodeFunction#on(IASTNullStatement)}
	 *   {@link ASTNodeFunction#on(IASTProblemStatement)}
	 *   {@link ASTNodeFunction#on(IASTReturnStatement)}
	 *   {@link ASTNodeFunction#on(IASTSwitchStatement)}
	 *   {@link ASTNodeFunction#on(IASTWhileStatement)}
	 *   {@link ASTNodeFunction#on(IGNUASTGotoStatement)}
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
	 * @return return value for nodes of type IASTStatement
	 */
	default T on(final IASTStatement statement) {
		return on((IASTNode) statement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param switchStatement
	 *            switchStatement
	 * @return return value for nodes of type IASTSwitchStatement
	 */
	default T on(final IASTSwitchStatement switchStatement) {
		return on((IASTStatement) switchStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTTokenList)}
	 *
	 * IASTToken.getPropertyInParent() values
	 *   {@link IASTAttribute#ARGUMENT_CLAUSE}
	 *   {@link IASTTokenList#NESTED_TOKEN}
	 * </pre>
	 * 
	 * @param token
	 *            token
	 * @return return value for nodes of type IASTToken
	 */
	default T on(final IASTToken token) {
		return on((IASTNode) token);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTToken)}.
	 *
	 * @param tokenList
	 *            tokenList
	 * @return return value for nodes of type IASTTokenList
	 */
	default T on(final IASTTokenList tokenList) {
		return on((IASTToken) tokenList);
	}
	
	/**
	 * Overrides {@link ASTNodeConsumer#on(IASTNode)}.
	 *
	 * @param translationUnit
	 *            translationUnit
	 * @return return value for nodes of type IASTTranslationUnit
	 */
	default T on(final IASTTranslationUnit translationUnit) {
		return on((IASTNode) translationUnit);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(IASTProblemTypeId)}
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
	 * @return return value for nodes of type IASTTypeId
	 */
	default T on(final IASTTypeId typeId) {
		return on((IASTNode) typeId);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param typeIdExpression
	 *            typeIdExpression
	 * @return return value for nodes of type IASTTypeIdExpression
	 */
	default T on(final IASTTypeIdExpression typeIdExpression) {
		return on((IASTExpression) typeIdExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param typeIdInitializerExpression
	 *            typeIdInitializerExpression
	 * @return return value for nodes of type IASTTypeIdInitializerExpression
	 */
	default T on(final IASTTypeIdInitializerExpression typeIdInitializerExpression) {
		return on((IASTExpression) typeIdInitializerExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param unaryExpression
	 *            unaryExpression
	 * @return return value for nodes of type IASTUnaryExpression
	 */
	default T on(final IASTUnaryExpression unaryExpression) {
		return on((IASTExpression) unaryExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param whileStatement
	 *            whileStatement
	 * @return return value for nodes of type IASTWhileStatement
	 */
	default T on(final IASTWhileStatement whileStatement) {
		return on((IASTStatement) whileStatement);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(ICASTDesignator)}.
	 *
	 * @param castArrayDesignator
	 *            cArrayDesignator
	 * @return return value for nodes of type ICASTArrayDesignator
	 */
	default T on(final ICASTArrayDesignator castArrayDesignator) {
		return on((ICASTDesignator) castArrayDesignator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTArrayModifier)}.
	 *
	 * @param castArrayModifier
	 *            cArrayModifier
	 * @return return value for nodes of type ICASTArrayModifier
	 */
	default T on(final ICASTArrayModifier castArrayModifier) {
		return on((IASTArrayModifier) castArrayModifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTInitializer)}.
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
	 * @return return value for nodes of type ICASTDesignatedInitializer
	 */
	default T on(final ICASTDesignatedInitializer castDesignatedInitializer) {
		return on((IASTInitializer) castDesignatedInitializer);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTNode)}.
	 *
	 * <pre>
	 * Overridden by
	 *   {@link ASTNodeFunction#on(ICASTArrayDesignator)}
	 *   {@link ASTNodeFunction#on(ICASTFieldDesignator)}
	 *   {@link ASTNodeFunction#on(IGCCASTArrayRangeDesignator)}
	 *
	 * ICASTDesignator.getPropertyInParent() values
	 *   {@link ICASTDesignatedInitializer#DESIGNATOR}
	 * </pre>
	 * 
	 * @param castDesignator
	 *            cDesignator
	 * @return return value for nodes of type ICASTDesignator
	 */
	default T on(final ICASTDesignator castDesignator) {
		return on((IASTNode) castDesignator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(ICASTDesignator)}.
	 *
	 * @param castFieldDesignator
	 *            cFieldDesignator
	 * @return return value for nodes of type ICASTFieldDesignator
	 */
	default T on(final ICASTFieldDesignator castFieldDesignator) {
		return on((ICASTDesignator) castFieldDesignator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTFunctionDeclarator)}.
	 *
	 * @param castKnRFunctionDeclarator
	 *            cKnRFunctionDeclarator
	 * @return return value for nodes of type ICASTKnRFunctionDeclarator
	 */
	default T on(final ICASTKnRFunctionDeclarator castKnRFunctionDeclarator) {
		return on((IASTFunctionDeclarator) castKnRFunctionDeclarator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTPointer)}.
	 *
	 * @param castPointer
	 *            cPointer
	 * @return return value for nodes of type ICASTPointer
	 */
	default T on(final ICASTPointer castPointer) {
		return on((IASTPointer) castPointer);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(ICASTDesignator)}.
	 *
	 * @param gccArrayRangeDesignator
	 *            gccArrayRangeDesignator
	 * @return return value for nodes of type IGCCASTArrayRangeDesignator
	 */
	default T on(final IGCCASTArrayRangeDesignator gccArrayRangeDesignator) {
		return on((ICASTDesignator) gccArrayRangeDesignator);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTAttributeSpecifier)}.
	 *
	 * @param gccAttributeSpecifier
	 *            gccAttributeSpecifier
	 * @return return value for nodes of type IGCCASTAttributeSpecifier
	 */
	default T on(final IGCCASTAttributeSpecifier gccAttributeSpecifier) {
		return on((IASTAttributeSpecifier) gccAttributeSpecifier);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTExpression)}.
	 *
	 * @param gnuCompoundStatementExpression
	 *            gnuCompoundStatementExpression
	 * @return return value for nodes of type IGNUASTCompoundStatementExpression
	 */
	default T on(final IGNUASTCompoundStatementExpression gnuCompoundStatementExpression) {
		return on((IASTExpression) gnuCompoundStatementExpression);
	}
	
	/**
	 * Overrides {@link ASTNodeFunction#on(IASTStatement)}.
	 *
	 * @param gnuGotoStatement
	 *            gnuGotoStatement
	 * @return return value for nodes of type IGNUASTGotoStatement
	 */
	default T on(final IGNUASTGotoStatement gnuGotoStatement) {
		return on((IASTStatement) gnuGotoStatement);
	}
}
