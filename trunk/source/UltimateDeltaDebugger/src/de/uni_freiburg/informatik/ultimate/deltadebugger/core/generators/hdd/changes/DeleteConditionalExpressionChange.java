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

import java.util.Arrays;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.HddChange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by conditional expression deletion.
 */
public class DeleteConditionalExpressionChange extends HddChange {
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
	public void updateDeferredChange(final Map<IPSTNode, HddChange> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(mConditionalExpressionNode, CombinedChange::new))
				.addChange(this);
	}
	
	/**
	 * Combined change.
	 */
	class CombinedChange extends HddChange {
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
				RewriteUtils.deleteNodeText(rewriter, mParts[0].getNode());
				RewriteUtils.replaceByWhitespace(rewriter, mTokColon);
				RewriteUtils.deleteNodeText(rewriter, mParts[1].getNode());
				RewriteUtils.replaceByWhitespace(rewriter, mTokQuestion);
				rewriter.replace(mParts[2].getNode(), mParts[2].mReplacement);
			} else if (count == 2) {
				if (mParts[0] == null) {
					// replace both results (keep condition and ? : tokens)
					rewriter.replace(mParts[1].getNode(), mParts[1].mReplacement);
					rewriter.replace(mParts[2].getNode(), mParts[2].mReplacement);
				} else {
					// delete condition and tokens and one of the results
					RewriteUtils.deleteNodeText(rewriter, mParts[0].getNode());
					RewriteUtils.replaceByWhitespace(rewriter, mTokQuestion);
					RewriteUtils.replaceByWhitespace(rewriter, mTokColon);
					if (mParts[1] != null) {
						RewriteUtils.deleteNodeText(rewriter, mParts[1].getNode());
					} else {
						RewriteUtils.deleteNodeText(rewriter, mParts[2].getNode());
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
