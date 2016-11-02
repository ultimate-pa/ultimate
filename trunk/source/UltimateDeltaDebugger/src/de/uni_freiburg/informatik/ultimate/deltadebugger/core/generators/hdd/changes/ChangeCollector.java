package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.parser.IToken;

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

public class ChangeCollector {
	private final Logger mLogger = Logger.getLogger(ChangeCollector.class);
	private final Map<IPSTRegularNode, List<CommaSeparatedChild>> mParentToCommaPositionMap;
	private final List<Change> mChanges = new ArrayList<>();

	public ChangeCollector(final Map<IPSTRegularNode, List<CommaSeparatedChild>> parentToCommaPositionMap) {
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

	public boolean addChange(final Change newChange) {
		newChange.setIndex(mChanges.size());
		mChanges.add(newChange);
		return true;
	}

	public boolean addDeleteAllTokensChange(final IPSTNode node) {
		final List<Token> tokens = TokenCollector.collect(node);
		if (tokens.isEmpty()) {
			return false;
		}

		// Tokens are not validated, we just want to delete them all.
		// However, at least ensure that parenthesis are always deleted in
		// pairs.
		if (!TokenUtils.isAllParenthesisBalanced(tokens)) {
			mLogger.trace("DeleteTokensChange skipped because of unbalanced parenthesis in " + node);
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
	 * @param fullReplacement
	 *            replacement to use in case changes that delete both operands are applied
	 */
	public boolean addDeleteBinaryExpressionOperandChange(final IPSTRegularNode operandNode,
			final String fullReplacement) {
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
			mLogger.trace(
					"DeleteBinaryExpressionOperand not supported because of missing operator token: " + operandNode);
			return false;
		}

		return addChange(new DeleteBinaryExpressionOperandChange(operandNode, binaryExpressionNode, tokens.get(0),
				fullReplacement));
	}

	public void addDeleteChange(final IPSTNode node) {
		addChange(new DeleteChange(node));
	}

	public void addDeleteConditionalDirectivesChange(final IPSTConditionalBlock block) {
		addChange(new DeleteConditionalDirectivesChange(block));
	}

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
			mLogger
					.trace("DeleteConditionalExpression not supported because of invalid property: " + property);
			return false;
		}

		final IPSTRegularNode conditionalExpressionNode = node.getRegularParent();
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(conditionalExpressionNode, IToken.tQUESTION, IToken.tCOLON);
		if (tokens[0] == null || tokens[1] == null) {
			mLogger
					.trace("DeleteConditionalExpression not supported because of missing operator tokens: "
							+ conditionalExpressionNode);
			return false;
		}

		return addChange(new DeleteConditionalExpressionChange(node, conditionalExpressionNode, tokens[0], tokens[1],
				position, replacement));
	}

	/**
	 * Replaces
	 *
	 * do body while (condition);
	 *
	 * by
	 *
	 * body condition;
	 *
	 * @param node
	 *            statement node
	 * @return true if a change as been added
	 */
	public boolean addDeleteDoStatementTokensChange(final IPSTRegularNode node) {
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(node, IToken.t_do, IToken.t_while, IToken.tLPAREN, IToken.tRPAREN);
		final Token tDO = tokens[0];
		final Token tWHILE = tokens[1];
		final Token tLPAREN = tokens[2];
		final Token tRPAREN = tokens[3];

		if (tDO == null || tWHILE == null) {
			return false;
		}

		return addChange(new Change(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tDO);
				replaceByWhitespace(rewriter, tWHILE);
				// Do no create unbalanced parentheses by only deleting one
				if (tLPAREN != null && tRPAREN != null) {
					replaceByWhitespace(rewriter, tLPAREN);
					replaceByWhitespace(rewriter, tRPAREN);
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
	 *
	 * for (declaration; condition; iteration) body
	 *
	 * by
	 *
	 * declaration; condition; iteration; body;
	 *
	 * @param node
	 *            statement node
	 * @param forStatement
	 *            IASTNode casted by caller
	 * @return true if a change as been added
	 */
	public boolean addDeleteForStatementTokensChange(final IPSTRegularNode node, final IASTForStatement forStatement) {
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(node, IToken.t_for, IToken.tLPAREN, IToken.tSEMI, IToken.tRPAREN);
		final Token tFOR = tokens[0];
		final Token tLPAREN = tokens[1];
		final Token tRPAREN = tokens[3];

		// In contrast to if and while, the parenthesis has to be removed,
		// because otherwise the contained statements are not valid syntax
		if (tFOR == null || tLPAREN == null || tRPAREN == null) {
			return false;
		}

		// Insert a semicolon after the right parenthesis or before the body
		// statement
		final int insertionOffset = getInsertionPoint(tRPAREN, node.findRegularChild(forStatement.getBody()));
		if (insertionOffset == -1) {
			return false;
		}

		return addChange(new Change(node) {

			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tFOR);
				replaceByWhitespace(rewriter, tLPAREN);
				replaceByWhitespace(rewriter, tRPAREN);
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
	 *
	 * if (expression) statement1 else statement2
	 *
	 * into
	 *
	 * expression; statement1 statement2
	 *
	 * If tokens are missing because they are part of macro expansions or other preprocessor code, and the if-statement
	 * cannot be converted as whole an else-token is removed alone.
	 *
	 * @param node
	 *            statement node
	 * @param ifStatement
	 *            IASTNode casted by caller
	 * @return true if a change as been added
	 */
	public boolean addDeleteIfStatementTokensChange(final IPSTRegularNode node, final IASTIfStatement ifStatement) {
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(node, IToken.t_if, IToken.tLPAREN, IToken.tRPAREN, IToken.t_else);
		final Token tIF = tokens[0];
		final Token tLPAREN = tokens[1];
		final Token tRPAREN = tokens[2];
		final Token tELSE = tokens[3];

		// If there is an else clause but we don't have the else-token, we
		// cannot delete the if-token
		if (ifStatement.getElseClause() != null && tELSE == null) {
			return false;
		}

		// Find an insertion point for the semicolon so the condition
		// expression can be converted into a statement. It can be inserted
		// after the right parenthesis or before the then-clause.
		final int insertionOffset = getInsertionPoint(tRPAREN, node.findRegularChild(ifStatement.getThenClause()));

		// If the if-token is missing or no insertion point for the semicolon
		// has been found, try to delete the else-token instead
		if (tIF == null || insertionOffset == -1) {
			if (tELSE != null) {
				return addChange(new Change(node) {
					@Override
					public void apply(final SourceRewriter rewriter) {
						replaceByWhitespace(rewriter, tELSE);
					}

					@Override
					public String toString() {
						return "Delete else token from " + getNode();
					}
				});
			}
			return false;
		}

		return addChange(new Change(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tIF);
				// Do no create unbalanced parentheses by only deleting one
				if (tLPAREN != null && tRPAREN != null) {
					replaceByWhitespace(rewriter, tLPAREN);
					replaceByWhitespace(rewriter, tRPAREN);
				}
				if (tELSE != null) {
					replaceByWhitespace(rewriter, tELSE);
				}
				rewriter.insert(insertionOffset, ";");
			}

			@Override
			public String toString() {
				return "Delete if statement tokens from " + getNode();
			}
		});
	}

	public boolean addDeleteTypeIdFromCastExpressionChange(final IPSTRegularNode typeIdNode) {
		final Token[] tokens =
				TokenUtils.getExpectedTokenArray(typeIdNode.getRegularParent(), IToken.tLPAREN, IToken.tRPAREN);
		final Token tLPAREN = tokens[0];
		final Token tRPAREN = tokens[1];

		if (tLPAREN == null || tRPAREN == null) {
			return false;
		}

		return addChange(new Change(typeIdNode) {

			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tLPAREN);
				replaceByWhitespace(rewriter, tRPAREN);
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
	 *
	 * while (condition) body
	 *
	 * by
	 *
	 * condition; body
	 *
	 * @param node
	 *            statement node
	 * @param whileStatement
	 *            IASTNode casted by caller
	 * @return true if a change as been added
	 */
	public boolean addDeleteWhileStatementTokensChange(final IPSTRegularNode node,
			final IASTWhileStatement whileStatement) {
		final Token[] tokens = TokenUtils.getExpectedTokenArray(node, IToken.t_while, IToken.tLPAREN, IToken.tRPAREN);
		final Token tWHILE = tokens[0];
		final Token tLPAREN = tokens[1];
		final Token tRPAREN = tokens[2];

		if (tWHILE == null) {
			return false;
		}

		// Insert a semicolon after the right parenthesis or before the body
		// statement
		final int insertionOffset = getInsertionPoint(tRPAREN, node.findRegularChild(whileStatement.getBody()));
		if (insertionOffset == -1) {
			return false;
		}

		return addChange(new Change(node) {
			@Override
			public void apply(final SourceRewriter rewriter) {
				replaceByWhitespace(rewriter, tWHILE);
				// Do no create unbalanced parentheses by only deleting one
				if (tLPAREN != null && tRPAREN != null) {
					replaceByWhitespace(rewriter, tLPAREN);
					replaceByWhitespace(rewriter, tRPAREN);
				}
				rewriter.insert(insertionOffset, ";");
			}

			@Override
			public String toString() {
				return "Delete while statement tokens from " + getNode();
			}
		});
	}

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
			mLogger.trace("DeleteWithCommaChange not supported because of missing comma: " + node);
			return false;
		}

		return addChange(new DeleteWithCommaChange(node, parent, commaPositions, keepOne));
	}

	public void addReplaceChange(final IPSTNode node, final String replacementString) {
		if (!RewriteUtils.skipEquivalentReplacement(node, replacementString)) {
			addChange(new ReplaceChange(node, replacementString));
		}
	}

	public List<Change> getChanges() {
		return mChanges;
	}
}
