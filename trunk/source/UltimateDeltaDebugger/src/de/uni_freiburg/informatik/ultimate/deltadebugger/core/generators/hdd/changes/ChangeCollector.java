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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.parser.IToken;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.CommaDeleter;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.HddChange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChild;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChildFinder;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change collector.
 */
public class ChangeCollector {
	private final ILogger mLogger;
	private final Map<IPSTRegularNode, List<CommaSeparatedChild>> mParentToCommaPositionMap;
	private final List<HddChange> mChanges = new ArrayList<>();
	
	/**
	 * @param logger
	 *            Logger.
	 * @param parentToCommaPositionMap
	 *            map (parent PST node -> comma position)
	 */
	public ChangeCollector(final ILogger logger,
			final Map<IPSTRegularNode, List<CommaSeparatedChild>> parentToCommaPositionMap) {
		mLogger = logger;
		mParentToCommaPositionMap = parentToCommaPositionMap;
	}
	
	private static int getInsertionPoint(final Token rparenToken, final IPSTRegularNode expecteRightSibling) {
		if (rparenToken != null) {
			return rparenToken.endOffset();
		}
		if (expecteRightSibling != null) {
			return expecteRightSibling.offset();
		}
		return -1;
	}
	
	/**
	 * @param newChange
	 *            New change.
	 * @return {@code true}
	 */
	public boolean addChange(final HddChange newChange) {
		newChange.setSequenceIndex(mChanges.size());
		mChanges.add(newChange);
		return true;
	}
	
	/**
	 * @param node
	 *            PST node.
	 * @return {@code false}
	 */
	public boolean addDeleteAllTokensChange(final IPSTNode node) {
		final List<Token> tokens = TokenCollector.collect(node);
		if (tokens.isEmpty()) {
			return false;
		}
		
		// Tokens are not validated, we just want to delete them all.
		// However, at least ensure that parenthesis are always deleted in
		// pairs.
		if (!TokenUtils.isAllParenthesesBalanced(tokens)) {
			mLogger.debug("DeleteTokensChange skipped because of unbalanced parenthesis in " + node);
			return false;
		}
		
		return addChange(new DeleteTokensChange(node, tokens));
	}
	
	/**
	 * Add a change to delete one binary expression operand together with the operator. If both operands are deleted the
	 * binary expression is replaced by the given string (deleting both operands and the operator would not be an
	 * expression anymore, causing syntax errors)
	 *
	 * @param operandNode
	 *            operand PST node
	 * @param altOperandReplacements
	 *            alternative replacements if the operand could not be deleted
	 * @return {@code true} iff a change has been added
	 */
	public boolean addDeleteBinaryExpressionOperandChange(final IPSTRegularNode operandNode,
			final List<String> altOperandReplacements) {
		final ASTNodeProperty property = operandNode.getAstNode().getPropertyInParent();
		if (property != IASTBinaryExpression.OPERAND_ONE && property != IASTBinaryExpression.OPERAND_TWO) {
			mLogger.warn("DeleteBinaryExpressionOperand not supported for operand node " + operandNode
					+ " with property " + property);
			return false;
		}
		
		// Get the tokens between child nodes and just assume that if there is
		// exactly one token it is the operator.
		final IPSTRegularNode binaryExpressionNode = operandNode.getRegularParent();
		final List<Token> tokens = TokenCollector.collect(binaryExpressionNode);
		if (tokens.size() != 1) {
			mLogger.debug(
					"DeleteBinaryExpressionOperand not supported because of missing operator token: " + operandNode);
			return addMultiReplaceChange(operandNode, altOperandReplacements);
		}
		
		return addChange(new DeleteBinaryExpressionOperandChange(operandNode, binaryExpressionNode, tokens.get(0),
				RewriteUtils.removeEquivalentReplacements(operandNode, altOperandReplacements)));
	}
	
	/**
	 * @param node
	 *            PST node.
	 */
	public void addDeleteChange(final IPSTNode node) {
		addChange(new DeleteChange(node));
	}
	
	/**
	 * @param block
	 *            PST block.
	 */
	public void addDeleteConditionalDirectivesChange(final IPSTConditionalBlock block) {
		addChange(new DeleteConditionalDirectivesChange(block));
	}
	
	/**
	 * @param node
	 *            PST node.
	 * @param replacement
	 *            replacement string
	 * @return {@code true} iff a change has been added
	 */
	public boolean addDeleteConditionalExpressionChange(final IPSTRegularNode node, final String replacement) {
		final ASTNodeProperty property = node.getAstNode().getPropertyInParent();
		int position;
		if (property == IASTConditionalExpression.LOGICAL_CONDITION) {
			position = 0;
		} else if (property == IASTConditionalExpression.POSITIVE_RESULT) {
			position = 1;
		} else if (property == IASTConditionalExpression.NEGATIVE_RESULT) {
			position = 2;
		} else {
			mLogger.debug("DeleteConditionalExpression not supported because of invalid property: " + property);
			return false;
		}
		
		// Do not replace something by itself...
		if (RewriteUtils.skipEquivalentReplacement(node, replacement)) {
			return false;
		}
		
		final IPSTRegularNode conditionalExpressionNode = node.getRegularParent();
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(conditionalExpressionNode, IToken.tQUESTION, IToken.tCOLON);
		if (tokens[0] == null || tokens[1] == null) {
			mLogger.debug("DeleteConditionalExpression not supported because of missing operator tokens: "
					+ conditionalExpressionNode);
			return false;
		}
		
		return addChange(new DeleteConditionalExpressionChange(node, conditionalExpressionNode, tokens[0], tokens[1],
				position, replacement));
	}
	
	/**
	 * Replaces
	 * {@code do body while (condition);}
	 * by
	 * {@code body condition;}.
	 *
	 * @param node
	 *            statement node
	 * @return {@code true} iff a change has been added
	 */
	public boolean addDeleteDoStatementTokensChange(final IPSTRegularNode node) {
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(node, IToken.t_do, IToken.t_while, IToken.tLPAREN, IToken.tRPAREN);
		final Token tokDo = tokens[0];
		final Token tokWhile = tokens[1];
		
		if (tokDo == null || tokWhile == null) {
			return false;
		}
		
		final Token tokLparen = tokens[2];
		final Token tokRparen = tokens[3];
		
		return addChange(new HddChange(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				RewriteUtils.replaceByWhitespace(rewriter, tokDo);
				RewriteUtils.replaceByWhitespace(rewriter, tokWhile);
				// Do no create unbalanced parentheses by only deleting one
				if (tokLparen != null && tokRparen != null) {
					RewriteUtils.replaceByWhitespace(rewriter, tokLparen);
					RewriteUtils.replaceByWhitespace(rewriter, tokRparen);
				}
			}
			
			@Override
			public String toString() {
				return "Delete do-while statement tokens from " + getNode();
			}
		});
	}
	
	/**
	 * Replaces
	 * {@code for (declaration; condition; iteration) body}
	 * by
	 * {@code declaration; condition; iteration; body;}.
	 *
	 * @param node
	 *            statement node
	 * @param forStatement
	 *            IASTNode casted by caller
	 * @return {@code true} iff a change has been added
	 */
	public boolean addDeleteForStatementTokensChange(final IPSTRegularNode node, final IASTForStatement forStatement) {
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(node, IToken.t_for, IToken.tLPAREN, IToken.tSEMI, IToken.tRPAREN);
		final Token tokFor = tokens[0];
		final Token tokLparen = tokens[1];
		final Token tokRparen = tokens[3];
		
		// In contrast to if and while, the parenthesis has to be removed,
		// because otherwise the contained statements are not valid syntax
		if (tokFor == null || tokLparen == null || tokRparen == null) {
			return false;
		}
		
		// Insert a semicolon after the right parenthesis or before the body
		// statement
		final int insertionOffset = getInsertionPoint(tokRparen, node.findRegularChild(forStatement.getBody()));
		if (insertionOffset == -1) {
			return false;
		}
		
		return addChange(new HddChange(node) {
			
			@Override
			public void apply(final SourceRewriter rewriter) {
				RewriteUtils.replaceByWhitespace(rewriter, tokFor);
				RewriteUtils.replaceByWhitespace(rewriter, tokLparen);
				RewriteUtils.replaceByWhitespace(rewriter, tokRparen);
				rewriter.insert(insertionOffset, ";");
			}
			
			@Override
			public String toString() {
				return "Delete for statement tokens from " + getNode();
			}
			
		});
	}
	
	/**
	 * Try to convert
	 * {@code if (expression) statement1 else statement2}
	 * into
	 * {@code expression; statement1 statement2}.
	 * If tokens are missing because they are part of macro expansions or other preprocessor code, and the if-statement
	 * cannot be converted as whole an else-token is removed alone.
	 *
	 * @param node
	 *            statement node
	 * @param ifStatement
	 *            IASTNode casted by caller
	 * @return {@code true} iff a change has been added
	 */
	public boolean addDeleteIfStatementTokensChange(final IPSTRegularNode node, final IASTIfStatement ifStatement) {
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(node, IToken.t_if, IToken.tLPAREN, IToken.tRPAREN, IToken.t_else);
		final Token tokElse = tokens[3];
		
		// If there is an else clause but we don't have the else-token, we
		// cannot delete the if-token
		if (ifStatement.getElseClause() != null && tokElse == null) {
			return false;
		}
		
		final Token tokIf = tokens[0];
		final Token tokRparen = tokens[2];
		
		// Find an insertion point for the semicolon so the condition
		// expression can be converted into a statement. It can be inserted
		// after the right parenthesis or before the then-clause.
		final int insertionOffset = getInsertionPoint(tokRparen, node.findRegularChild(ifStatement.getThenClause()));
		
		// If the if-token is missing or no insertion point for the semicolon
		// has been found, try to delete the else-token instead
		if (tokIf == null || insertionOffset == -1) {
			if (tokElse != null) {
				return addChange(new HddChange(node) {
					@Override
					public void apply(final SourceRewriter rewriter) {
						RewriteUtils.replaceByWhitespace(rewriter, tokElse);
					}
					
					@Override
					public String toString() {
						return "Delete else token from " + getNode();
					}
				});
			}
			return false;
		}
		
		final Token tokLparen = tokens[1];
		
		return addChange(new HddChange(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				RewriteUtils.replaceByWhitespace(rewriter, tokIf);
				// Do no create unbalanced parentheses by only deleting one
				if (tokLparen != null && tokRparen != null) {
					RewriteUtils.replaceByWhitespace(rewriter, tokLparen);
					RewriteUtils.replaceByWhitespace(rewriter, tokRparen);
				}
				if (tokElse != null) {
					RewriteUtils.replaceByWhitespace(rewriter, tokElse);
				}
				rewriter.insert(insertionOffset, ";");
			}
			
			@Override
			public String toString() {
				return "Delete if statement tokens from " + getNode();
			}
		});
	}
	
	/**
	 * @param typeIdNode
	 *            PST node.
	 * @return {@code true} iff a change has been added
	 */
	public boolean addDeleteTypeIdFromCastExpressionChange(final IPSTRegularNode typeIdNode) {
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(typeIdNode.getRegularParent(), IToken.tLPAREN, IToken.tRPAREN);
		final Token tokLparen = tokens[0];
		final Token tokRparen = tokens[1];
		
		if (tokLparen == null || tokRparen == null) {
			return false;
		}
		
		return addChange(new HddChange(typeIdNode) {
			
			@Override
			public void apply(final SourceRewriter rewriter) {
				RewriteUtils.replaceByWhitespace(rewriter, tokLparen);
				RewriteUtils.replaceByWhitespace(rewriter, tokRparen);
				RewriteUtils.replaceByWhitespace(rewriter, getNode());
			}
			
			@Override
			public String toString() {
				return "Delete typeid from cast expression " + getNode();
			}
		});
	}
	
	/**
	 * Replaces
	 * {@code while (condition) body}
	 * by
	 * {@code condition; body}.
	 *
	 * @param node
	 *            statement node
	 * @param whileStatement
	 *            IASTNode casted by caller
	 * @return {@code true} iff a change has been added
	 */
	public boolean addDeleteWhileStatementTokensChange(final IPSTRegularNode node,
			final IASTWhileStatement whileStatement) {
		final Token[] tokens = TokenUtils.getExpectedTokenArray(node, IToken.t_while, IToken.tLPAREN, IToken.tRPAREN);
		final Token tokWhile = tokens[0];
		
		if (tokWhile == null) {
			return false;
		}
		
		final Token tokRparen = tokens[2];
		
		// Insert a semicolon after the right parenthesis or before the body
		// statement
		final int insertionOffset = getInsertionPoint(tokRparen, node.findRegularChild(whileStatement.getBody()));
		if (insertionOffset == -1) {
			return false;
		}
		
		final Token tokLparen = tokens[1];
		
		return addChange(new HddChange(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				RewriteUtils.replaceByWhitespace(rewriter, tokWhile);
				// Do no create unbalanced parentheses by only deleting one
				if (tokLparen != null && tokRparen != null) {
					RewriteUtils.replaceByWhitespace(rewriter, tokLparen);
					RewriteUtils.replaceByWhitespace(rewriter, tokRparen);
				}
				rewriter.insert(insertionOffset, ";");
			}
			
			@Override
			public String toString() {
				return "Delete while statement tokens from " + getNode();
			}
		});
	}
	
	/**
	 * @param node
	 *            PST node.
	 * @param keepOne
	 *            {@code true} iff one element should be kept
	 * @return {@code true} iff a change has been added
	 */
	public boolean addDeleteWithCommaChange(final IPSTRegularNode node, final boolean keepOne) {
		final IPSTRegularNode parent = node.getRegularParent();
		final ASTNodeProperty childProperty = ASTNodeUtils.getPropertyOfCommaSeparatedChildNodes(parent.getAstNode());
		if (childProperty == null || node.getAstNode().getPropertyInParent() != childProperty) {
			mLogger.warn("DeleteWithCommaChange not supported for node " + node + " with property "
					+ node.getAstNode().getPropertyInParent());
			return false;
		}

		final List<CommaSeparatedChild> commaPositions = mParentToCommaPositionMap.computeIfAbsent(parent,
				n -> CommaSeparatedChildFinder.runWithVarArgsSupport(n, childProperty));
		if (keepOne && commaPositions.size() <= 1) {
			return false;
		}

		if (!CommaDeleter.isDeletionWithCommaPossible(node, commaPositions)) {
			mLogger.debug("DeleteWithCommaChange not supported because of missing comma: " + node);
			return false;
		}
		
		return addChange(new DeleteWithCommaChange(node, parent, commaPositions, keepOne));
	}
	
	/**
	 * Add a change to delete the varargs placeholder token "..." like a regular parameter declaration including the
	 * leading comma.
	 * 
	 * @param parent
	 *            PST node of the standard function declarator ast node.
	 * @param astNode
	 *            AST node of the standard function declarator.
	 * @param keepOne
	 *            {@code true} iff one element should be kept
	 * @return {@code true} iff a change was added
	 */
	public boolean addDeleteVarArgsChange(final IPSTRegularNode parent, final IASTStandardFunctionDeclarator astNode,
			boolean keepOne) {
		if (!astNode.takesVarArgs()) {
			return false;
		}
		final List<Token> tokens = TokenCollector.collect(parent);
		final Token token = tokens.stream().filter(t -> t.getType() == IToken.tELLIPSIS).findAny().orElse(null);
		if (token == null) {
			mLogger.debug("DeleteVarArgsChange not supported because of missing ellipsis token: " + parent);
			return false;
		}

		final List<CommaSeparatedChild> commaPositions = mParentToCommaPositionMap.computeIfAbsent(parent,
				n -> CommaSeparatedChildFinder.runWithVarArgsSupport(n,
						IASTStandardFunctionDeclarator.FUNCTION_PARAMETER));
		if (keepOne && commaPositions.size() <= 1) {
			return false;
		}

		if (!CommaDeleter.isDeletionWithCommaPossible(token, commaPositions)) {
			mLogger.debug("DeleteVarArgs not supported because of missing comma: " + token);
			return false;
		}

		return addChange(new DeleteWithCommaChange(parent, commaPositions, keepOne, token));
	}
	

	/**
	 * Delete an element with comma or replace it alternatively.
	 *
	 * @param node
	 *            PST node.
	 * @param keepOne
	 *            {@code true} iff one element should be kept
	 * @param replacements
	 *            list of alternative replacements if deletion fails
	 * @return {@code true} iff a change has been added
	 * @return
	 */
	public boolean addDeleteWithCommaOrReplaceChange(final IPSTRegularNode node, final boolean keepOne,
			final List<String> replacements) {
		final IPSTRegularNode parent = node.getRegularParent();
		final ASTNodeProperty childProperty = ASTNodeUtils.getPropertyOfCommaSeparatedChildNodes(parent.getAstNode());
		if (childProperty == null || node.getAstNode().getPropertyInParent() != childProperty) {
			mLogger.warn("DeleteWithCommaChange not supported for node " + node + " with property "
					+ node.getAstNode().getPropertyInParent());
			return addMultiReplaceChange(node, replacements);
		}

		final List<CommaSeparatedChild> commaPositions = mParentToCommaPositionMap.computeIfAbsent(parent,
				n -> CommaSeparatedChildFinder.runWithVarArgsSupport(n, childProperty));
		if (keepOne && commaPositions.size() <= 1) {
			return addMultiReplaceChange(node, replacements);
		}

		if (!CommaDeleter.isDeletionWithCommaPossible(node, commaPositions)) {
			mLogger.debug("DeleteWithCommaChange not supported because of missing comma: " + node);
			return addMultiReplaceChange(node, replacements);
		}

		final List<String> validReplacements = RewriteUtils.removeEquivalentReplacements(node, replacements);
		return addChange(new DeleteWithCommaChange(node, parent, commaPositions, keepOne) {
			@Override
			public Optional<HddChange> createAlternativeChange() {
				return validReplacements.isEmpty() ? Optional.empty()
						: Optional.of(new MultiReplaceChange(getNode(), validReplacements));
			}

			@Override
			public String toString() {
				return super.toString() + " with alternative replacements ("
						+ validReplacements.stream().collect(Collectors.joining(", ")) + ")";
			}
		});
	}


	/**
	 * Split initialization expression from a declaration by replacing the equals character by a semicolon. This may
	 * allow a deletion of the declaration statement in following HDD applications, while keeping the expression
	 * side-effects.
	 * 
	 * Currently only done for declaration statements with a single declarator and where the initializer is an
	 * expression (and not an initializer list).
	 * 
	 * @param node
	 *            The equals initializer node.
	 * @param astNode
	 *           The AST node, cast done by caller.
	 * @return {@code true} iff a change has been added
	 */
	public boolean addChangeToSplitInitializerExpressionFromDeclaration(final IPSTNode node,
			IASTEqualsInitializer astNode) {
		// Is the initializer clause an expression?
		final IASTInitializerClause clause = astNode.getInitializerClause();
		if (!(clause instanceof IASTExpression)) {
			return false;
		}
		// Traverse up the tree and ensure this initializer is part of a statement with only one declarator.
		if (astNode.getPropertyInParent() != IASTDeclarator.INITIALIZER) {
			return false;
		}
		final IASTDeclarator declarator = (IASTDeclarator) astNode.getParent();
		if (declarator.getPropertyInParent() != IASTSimpleDeclaration.DECLARATOR) {
			return false;
		}
		final IASTSimpleDeclaration declaration = (IASTSimpleDeclaration) declarator.getParent();
		if (declaration.getDeclarators().length != 1) {
			return false;
		}
		if (declaration.getPropertyInParent() != IASTDeclarationStatement.DECLARATION) {
			return false;
		}

		// Now find the assignment token
		final Token[] tokens = TokenUtils.getExpectedTokenArray(node, IToken.tASSIGN);
		if (tokens[0] == null) {
			return false;
		}
		return addChange(new HddChange(node) {
			@Override
			public void apply(SourceRewriter rewriter) {
				rewriter.replace(tokens[0], ";");
			}

			@Override
			public String toString() {
				return "Split initializer expression from declaration statement " + getNode();
			}
		});
	}	
	

	/**
	 * Deletes an array subscript expression{@literal <array>[<subscript>]}. Can try alternative replacements if
	 * deletion fails.
	 *
	 * @param node
	 *            array subscript expression node
	 * @param replacements
	 *            list of alternative replacements
	 * @return
	 */
	public boolean addArraySubscriptChange(final IPSTRegularNode node, final List<String> replacements) {
		final IPSTNode parent = node.getRegularParent();
		final Token[] tokens = TokenUtils.getExpectedTokenArray(parent, IToken.tLBRACKET, IToken.tRBRACKET);
		if (tokens[0] == null || tokens[1] == null) {
			mLogger.debug(
					"DeleteArraySubscript not supported because of missing bracket tokens in parent node " + parent);
			return false;
		}
		final List<String> validReplacements = RewriteUtils.removeEquivalentReplacements(node, replacements);
		return addChange(new HddChange(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				RewriteUtils.replaceByWhitespace(rewriter, tokens[0]);
				RewriteUtils.replaceByWhitespace(rewriter, getNode());
				RewriteUtils.replaceByWhitespace(rewriter, tokens[1]);
			}

			@Override
			public Optional<HddChange> createAlternativeChange() {
				return validReplacements.isEmpty() ? Optional.empty()
						: Optional.of(new MultiReplaceChange(getNode(), validReplacements));
			}

			@Override
			public String toString() {
				return "Delete or replace array subscript " + getNode();
			}
		});
	}


	/**
	 * @param node
	 *            PST node.
	 * @param replacementString
	 *            replacement string
	 */
	public void addReplaceChange(final IPSTNode node, final String replacementString) {
		if (!RewriteUtils.skipEquivalentReplacement(node, replacementString)) {
			addChange(new ReplaceChange(node, replacementString));
		}
	}
	
	/**
	 * @param node
	 *            PST node to be replacement.
	 * @param replacementStrings
	 *            list of replacements to be tested in the given order
	 * @return {@code true} iff a change was added
	 */
	public boolean addMultiReplaceChange(final IPSTNode node, final List<String> replacementStrings) {
		final List<String> validReplacements = RewriteUtils.removeEquivalentReplacements(node, replacementStrings);
		if (!validReplacements.isEmpty()) {
			return addChange(new MultiReplaceChange(node, validReplacements));
		}
		return false;
	}
	
	public List<HddChange> getChanges() {
		return mChanges;
	}
}
