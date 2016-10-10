package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.Arrays;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public class DeleteConditionalExpressionChange extends Change {
	class CombinedChange extends Change {
		DeleteConditionalExpressionChange[] parts = new DeleteConditionalExpressionChange[3];

		CombinedChange(final IPSTNode node) {
			super(node);
		}

		void addChange(final DeleteConditionalExpressionChange change) {
			parts[change.position] = change;
		}

		@Override
		public void apply(final SourceRewriter rewriter) {
			final long count = Arrays.stream(parts).filter(Objects::nonNull).count();
			if (count == 3) {
				// Replace whole expression by the replacement of the negative result
				deleteNodeText(rewriter, parts[0].getNode());
				replaceByWhitespace(rewriter, tCOLON);
				deleteNodeText(rewriter, parts[1].getNode());
				replaceByWhitespace(rewriter, tQUESTION);
				rewriter.replace(parts[2].getNode(), parts[2].replacement);

			} else if (count == 2) {
				if (parts[0] == null) {
					// replace both results (keep condition and ? : tokens)
					rewriter.replace(parts[1].getNode(), parts[1].replacement);
					rewriter.replace(parts[2].getNode(), parts[2].replacement);
				} else {
					// delete condition and tokens and one of the results
					deleteNodeText(rewriter, parts[0].getNode());
					replaceByWhitespace(rewriter, tQUESTION);
					replaceByWhitespace(rewriter, tCOLON);
					if (parts[1] != null) {
						deleteNodeText(rewriter, parts[1].getNode());
					} else {
						deleteNodeText(rewriter, parts[2].getNode());
					}
				}
			} else if (count == 1) {
				// replace one of the three expressions
				if (parts[0] != null) {
					rewriter.replace(parts[0].getNode(), parts[0].replacement);
				} else if (parts[1] != null) {
					rewriter.replace(parts[1].getNode(), parts[1].replacement);
				} else {
					rewriter.replace(parts[2].getNode(), parts[2].replacement);
				}
			}
		}

	}

	final IPSTRegularNode conditionalExpressionNode;
	final int position;
	final Token tQUESTION;
	final Token tCOLON;

	final String replacement;

	public DeleteConditionalExpressionChange(final IPSTRegularNode node,
			final IPSTRegularNode conditionalExpressionNode, final Token tQUESTION, final Token tCOLON,
			final int position, final String replacement) {
		super(node);
		this.conditionalExpressionNode = Objects.requireNonNull(conditionalExpressionNode);
		this.position = position;
		this.tQUESTION = Objects.requireNonNull(tQUESTION);
		this.tCOLON = Objects.requireNonNull(tCOLON);
		this.replacement = Objects.requireNonNull(replacement);
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
		return "Delete/Replace conditional expression part " + getNode() + " by \"" + replacement + "\"" + "(from "
				+ conditionalExpressionNode + ")";
	}

	@Override
	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(conditionalExpressionNode, CombinedChange::new))
				.addChange(this);
	}
}