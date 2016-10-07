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
	class CombinedChange extends Change {
		List<IPSTNode> operandsToDelete = new ArrayList<>();

		CombinedChange(final IPSTNode node) {
			super(node);
		}

		void addOperand(final IPSTNode child) {
			operandsToDelete.add(child);
		}

		@Override
		public void apply(final SourceRewriter rewriter) {
			if (operandsToDelete.size() == 1) {
				deleteNodeText(rewriter, operandsToDelete.get(0));
				replaceByWhitespace(rewriter, operatorPosition);
			} else if (operandsToDelete.size() == 2) {
				rewriter.replace(operandsToDelete.get(0), fullReplacement);
				replaceByWhitespace(rewriter, operatorPosition);
				deleteNodeText(rewriter, operandsToDelete.get(1));
			} else {
				throw new IllegalStateException("invalid number of operands to delete: " + operandsToDelete.size());
			}
		}

	}

	final IPSTRegularNode binaryExpressionNode;
	final ISourceRange operatorPosition;

	final String fullReplacement;

	public DeleteBinaryExpressionOperandChange(final IPSTRegularNode operandNode,
			final IPSTRegularNode binaryExpressionNode, final ISourceRange operatorPosition,
			final String fullReplacement) {
		super(operandNode);
		this.binaryExpressionNode = Objects.requireNonNull(binaryExpressionNode);
		this.operatorPosition = Objects.requireNonNull(operatorPosition);
		this.fullReplacement = Objects.requireNonNull(fullReplacement);
	}

	@Override
	public void apply(final SourceRewriter rewriter) {
		// no immedate modifiation possible
	}

	@Override
	public boolean hasDeferredChange() {
		return true;
	}

	@Override
	public String toString() {
		return "Delete binary expression operand " + getNode() + " (from " + binaryExpressionNode + ")";
	}

	@Override
	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(binaryExpressionNode, CombinedChange::new))
				.addOperand(getNode());
	}
}