package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public class DeleteBinaryExpressionOperandChange extends Change {
	private final IPSTRegularNode mBinaryExpressionNode;
	private final ISourceRange mOperatorPosition;
	private final String mFullReplacement;
	
	
	class CombinedChange extends Change {
		private List<IPSTNode> mOperandsToDelete = new ArrayList<>();

		CombinedChange(final IPSTNode node) {
			super(node);
		}

		void addOperand(final IPSTNode child) {
			mOperandsToDelete.add(child);
		}

		@Override
		public void apply(final SourceRewriter rewriter) {
			if (mOperandsToDelete.size() == 1) {
				deleteNodeText(rewriter, mOperandsToDelete.get(0));
				replaceByWhitespace(rewriter, mOperatorPosition);
			} else if (mOperandsToDelete.size() == 2) {
				rewriter.replace(mOperandsToDelete.get(0), mFullReplacement);
				replaceByWhitespace(rewriter, mOperatorPosition);
				deleteNodeText(rewriter, mOperandsToDelete.get(1));
			} else {
				throw new IllegalStateException("invalid number of operands to delete: " + mOperandsToDelete.size());
			}
		}

	}

	

	public DeleteBinaryExpressionOperandChange(final IPSTRegularNode operandNode,
			final IPSTRegularNode binaryExpressionNode, final ISourceRange operatorPosition,
			final String fullReplacement) {
		super(operandNode);
		mBinaryExpressionNode = Objects.requireNonNull(binaryExpressionNode);
		mOperatorPosition = Objects.requireNonNull(operatorPosition);
		mFullReplacement = Objects.requireNonNull(fullReplacement);
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
		return "Delete binary expression operand " + getNode() + " (from " + mBinaryExpressionNode + ")";
	}

	@Override
	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(mBinaryExpressionNode, CombinedChange::new))
				.addOperand(getNode());
	}
}
