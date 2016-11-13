package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.Arrays;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by conditional expression deletion.
 */
public class DeleteConditionalExpressionChange extends Change {
	private static final int NUM_OPERANDS = 3;
	
	private final IPSTRegularNode mConditionalExpressionNode;
	private final int mPosition;
	private final Token mTokQuestion;
	private final Token mTokColon;
	
	private final String mReplacement;
	
	/**
	 * @param node
	 *            PST node.
	 * @param conditionalExpressionNode
	 *            condition expression PST node
	 * @param tokQuestion
	 *            question token
	 * @param tokColon
	 *            colon token
	 * @param position
	 *            position
	 * @param replacement
	 *            replacement
	 */
	public DeleteConditionalExpressionChange(final IPSTRegularNode node,
			final IPSTRegularNode conditionalExpressionNode, final Token tokQuestion, final Token tokColon,
			final int position, final String replacement) {
		super(node);
		mConditionalExpressionNode = Objects.requireNonNull(conditionalExpressionNode);
		mPosition = position;
		mTokQuestion = Objects.requireNonNull(tokQuestion);
		mTokColon = Objects.requireNonNull(tokColon);
		mReplacement = Objects.requireNonNull(replacement);
		if (position < 0 || position > 2) {
			throw new IllegalArgumentException();
		}
	}
	
	@Override
	public void apply(final SourceRewriter rewriter) {
		// no immediate modification possible
	}
	
	@Override
	public boolean hasDeferredChange() {
		return true;
	}
	
	@Override
	public String toString() {
		return "Delete/Replace conditional expression part " + getNode() + " by \"" + mReplacement + "\"" + "(from "
				+ mConditionalExpressionNode + ")";
	}
	
	@Override
	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(mConditionalExpressionNode, CombinedChange::new))
				.addChange(this);
	}
	
	/**
	 * Combined change.
	 */
	class CombinedChange extends Change {
		private final DeleteConditionalExpressionChange[] mParts = new DeleteConditionalExpressionChange[NUM_OPERANDS];
		
		CombinedChange(final IPSTNode node) {
			super(node);
		}
		
		void addChange(final DeleteConditionalExpressionChange change) {
			mParts[change.mPosition] = change;
		}
		
		@Override
		public void apply(final SourceRewriter rewriter) {
			final long count = Arrays.stream(mParts).filter(Objects::nonNull).count();
			if (count == NUM_OPERANDS) {
				// Replace whole expression by the replacement of the negative result
				deleteNodeText(rewriter, mParts[0].getNode());
				replaceByWhitespace(rewriter, mTokColon);
				deleteNodeText(rewriter, mParts[1].getNode());
				replaceByWhitespace(rewriter, mTokQuestion);
				rewriter.replace(mParts[2].getNode(), mParts[2].mReplacement);
			} else if (count == 2) {
				if (mParts[0] == null) {
					// replace both results (keep condition and ? : tokens)
					rewriter.replace(mParts[1].getNode(), mParts[1].mReplacement);
					rewriter.replace(mParts[2].getNode(), mParts[2].mReplacement);
				} else {
					// delete condition and tokens and one of the results
					deleteNodeText(rewriter, mParts[0].getNode());
					replaceByWhitespace(rewriter, mTokQuestion);
					replaceByWhitespace(rewriter, mTokColon);
					if (mParts[1] != null) {
						deleteNodeText(rewriter, mParts[1].getNode());
					} else {
						deleteNodeText(rewriter, mParts[2].getNode());
					}
				}
			} else if (count == 1) {
				// replace one of the three expressions
				if (mParts[0] != null) {
					rewriter.replace(mParts[0].getNode(), mParts[0].mReplacement);
				} else if (mParts[1] != null) {
					rewriter.replace(mParts[1].getNode(), mParts[1].mReplacement);
				} else {
					rewriter.replace(mParts[2].getNode(), mParts[2].mReplacement);
				}
			}
		}
	}
}
