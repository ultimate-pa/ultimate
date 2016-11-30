package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.parser.IToken;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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
	private final List<Change> mChanges = new ArrayList<>();
	
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
	public boolean addChange(final Change newChange) {
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
		if (!TokenUtils.isAllParenthesisBalanced(tokens)) {
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
	@SuppressWarnings("squid:S1698")
	public boolean addDeleteBinaryExpressionOperandChange(final IPSTRegularNode operandNode,
			final List<String> altOperandReplacements) {
		final ASTNodeProperty property = operandNode.getASTNode().getPropertyInParent();
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
	@SuppressWarnings("squid:S1698")
	public boolean addDeleteConditionalExpressionChange(final IPSTRegularNode node, final String replacement) {
		final ASTNodeProperty property = node.getASTNode().getPropertyInParent();
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
		
		return addChange(new Change(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tokDo);
				replaceByWhitespace(rewriter, tokWhile);
				// Do no create unbalanced parentheses by only deleting one
				if (tokLparen != null && tokRparen != null) {
					replaceByWhitespace(rewriter, tokLparen);
					replaceByWhitespace(rewriter, tokRparen);
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
		
		return addChange(new Change(node) {
			
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tokFor);
				replaceByWhitespace(rewriter, tokLparen);
				replaceByWhitespace(rewriter, tokRparen);
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
				return addChange(new Change(node) {
					@Override
					public void apply(final SourceRewriter rewriter) {
						replaceByWhitespace(rewriter, tokElse);
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
		
		return addChange(new Change(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tokIf);
				// Do no create unbalanced parentheses by only deleting one
				if (tokLparen != null && tokRparen != null) {
					replaceByWhitespace(rewriter, tokLparen);
					replaceByWhitespace(rewriter, tokRparen);
				}
				if (tokElse != null) {
					replaceByWhitespace(rewriter, tokElse);
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
		
		return addChange(new Change(typeIdNode) {
			
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tokLparen);
				replaceByWhitespace(rewriter, tokRparen);
				replaceByWhitespace(rewriter, getNode());
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
		
		return addChange(new Change(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tokWhile);
				// Do no create unbalanced parentheses by only deleting one
				if (tokLparen != null && tokRparen != null) {
					replaceByWhitespace(rewriter, tokLparen);
					replaceByWhitespace(rewriter, tokRparen);
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
	@SuppressWarnings("squid:S1698")
	public boolean addDeleteWithCommaChange(final IPSTRegularNode node, final boolean keepOne) {
		final IPSTRegularNode parent = node.getRegularParent();
		final ASTNodeProperty childProperty = ASTNodeUtils.getPropertyOfCommaSeparatedChildNodes(parent.getASTNode());
		if (childProperty == null || node.getASTNode().getPropertyInParent() != childProperty) {
			mLogger.warn("DeleteWithCommaChange not supported for node " + node + " with property "
					+ node.getASTNode().getPropertyInParent());
			return false;
		}
		
		final List<CommaSeparatedChild> commaPositions = mParentToCommaPositionMap.computeIfAbsent(parent,
				n -> CommaSeparatedChildFinder.run(n, childProperty));
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
	 * The varargs token "..." is not a node in the PST and so it cannot be deleted with the existing
	 * {@code CommaDeleter} implementation to delete it like the other comma separated nodes. A better solution would be
	 * to change the CommaDeleter to not require a valid node and/or add a special node for this token to the PST. This
	 * workaround just deletes the "..."-token independently from the other parameters. To prevent syntax errors because
	 * of trailing comma, it should only be used if there are not other parameters.
	 * 
	 * @param node
	 *            PST node
	 * @param astNode
	 *            standard function declarator
	 * @return {@code true} iff a change was added
	 */
	public boolean addDeleteVarArgsChange(final IPSTRegularNode node, final IASTStandardFunctionDeclarator astNode) {
		if (!astNode.takesVarArgs()) {
			mLogger.warn("DeleteVarArgsChange not supported for node " + node + " because it does not take varargs");
			return false;
		}
		final List<Token> tokens = TokenCollector.collect(node);
		final Token token = tokens.stream().filter(t -> t.getType() == IToken.tELLIPSIS).findAny().orElse(null);
		if (token == null) {
			mLogger.debug("DeleteVarArgsChange not supported because of missing ellipsis: " + node);
			return false;
		}
		
		return addChange(new Change(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, token);
			}
			
			@Override
			public String toString() {
				return "Delete varargs from function declarator " + getNode();
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
	
	public List<Change> getChanges() {
		return mChanges;
	}
}
