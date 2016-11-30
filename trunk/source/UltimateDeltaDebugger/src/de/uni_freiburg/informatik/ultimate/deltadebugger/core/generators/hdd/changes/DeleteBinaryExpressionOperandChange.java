package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation.PSTVisitorWithResult;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by binary expression operand deletion.
 */
public class DeleteBinaryExpressionOperandChange extends Change {
	private final IPSTRegularNode mBinaryExpressionNode;
	private final ISourceRange mOperatorPosition;
	private final List<String> mAlternativeOperandReplacements;
	
	/**
	 * @param operandNode
	 *            Operand PST node.
	 * @param binaryExpressionNode
	 *            binary expression PST node
	 * @param operatorPosition
	 *            operator position
	 * @param alternativeOperandReplacements
	 *            alternative operand replacement strings
	 */
	public DeleteBinaryExpressionOperandChange(final IPSTRegularNode operandNode,
			final IPSTRegularNode binaryExpressionNode, final ISourceRange operatorPosition,
			final List<String> alternativeOperandReplacements) {
		super(operandNode);
		mBinaryExpressionNode = Objects.requireNonNull(binaryExpressionNode);
		mOperatorPosition = Objects.requireNonNull(operatorPosition);
		mAlternativeOperandReplacements = Objects.requireNonNull(alternativeOperandReplacements);
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
		return "Delete binary expression operand " + getNode() + " (from " + mBinaryExpressionNode
				+ ") or replace by one of ["
				+ mAlternativeOperandReplacements.stream().map(s -> "\"" + s + "\"").collect(Collectors.joining(", "))
				+ "])";
	}

	@Override
	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(mBinaryExpressionNode, CombinedChange::new))
				.addOperandChange(this);
	}
	
	@Override
	public Optional<Change> createAlternativeChange() {
		if (!mAlternativeOperandReplacements.isEmpty()) {
			return Optional.of(new MultiReplaceChange(getNode(), mAlternativeOperandReplacements));
		}
		return Optional.empty();
	}

	
	/**
	 * Combined change.
	 */
	static class CombinedChange extends Change {
		private final List<DeleteBinaryExpressionOperandChange> mOperandChanges = new ArrayList<>();
		
		CombinedChange(final IPSTNode node) {
			super(node);
		}
		
		void addOperandChange(final DeleteBinaryExpressionOperandChange change) {
			mOperandChanges.add(change);
		}
		
		@Override
		public void apply(final SourceRewriter rewriter) {
			if (mOperandChanges.size() == 1) {
				deleteNodeText(rewriter, mOperandChanges.get(0).getNode());
				replaceByWhitespace(rewriter, mOperandChanges.get(0).mOperatorPosition);
				return;
			}
			if (mOperandChanges.size() != 2) {
				throw new IllegalStateException("invalid number of operands to delete: " + mOperandChanges.size());
			}
				
			// delete the larger operand and immediately replace the other one (if possible)
			final DeleteBinaryExpressionOperandChange lhs = mOperandChanges.get(0);
			final DeleteBinaryExpressionOperandChange rhs = mOperandChanges.get(1);
			if (lhs.mAlternativeOperandReplacements.isEmpty() && rhs.mAlternativeOperandReplacements.isEmpty()) {
				throw new ChangeConflictException("Unable to delete one operand and replace the other one");
			}
			
			int deleteIndex;
			if (lhs.mAlternativeOperandReplacements.isEmpty() || rhs.mAlternativeOperandReplacements.isEmpty()) {
				// can only replace one of both so there is no choice
				deleteIndex = lhs.mAlternativeOperandReplacements.isEmpty() ? 0 : 1;
			} else {
				// prefer to delete the larger one
				deleteIndex = countChildren(lhs.getNode()) >= countChildren(rhs.getNode()) ? 0 : 1;
			}

			deleteNodeText(rewriter, mOperandChanges.get(deleteIndex).getNode());
			replaceByWhitespace(rewriter, lhs.mOperatorPosition);
			rewriter.replace(mOperandChanges.get(1 - deleteIndex).getNode(),
					mOperandChanges.get(1 - deleteIndex).mAlternativeOperandReplacements.get(0));
		}

		private static int countChildren(final IPSTNode node) {
			final PSTVisitorWithResult<Integer> action = new PSTVisitorWithResult<Integer>() {
				@Override
				public int defaultVisit(final IPSTNode node) {
					setResult(getResult().orElse(0) + 1);
					return PROCESS_CONTINUE;
				}
			};
			node.accept(action);
			return action.getResult().orElse(0);
		}
	}
}
