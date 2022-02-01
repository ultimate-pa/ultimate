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
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.HddChange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation.PSTVisitorWithResult;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by binary expression operand deletion.
 */
public class DeleteBinaryExpressionOperandChange extends HddChange {
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
	public void updateDeferredChange(final Map<IPSTNode, HddChange> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(mBinaryExpressionNode, CombinedChange::new))
				.addOperandChange(this);
	}
	
	@Override
	public Optional<HddChange> createAlternativeChange() {
		if (!mAlternativeOperandReplacements.isEmpty()) {
			return Optional.of(new MultiReplaceChange(getNode(), mAlternativeOperandReplacements));
		}
		return Optional.empty();
	}

	
	/**
	 * Combined change.
	 */
	static class CombinedChange extends HddChange {
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
				RewriteUtils.deleteNodeText(rewriter, mOperandChanges.get(0).getNode());
				RewriteUtils.replaceByWhitespace(rewriter, mOperandChanges.get(0).mOperatorPosition);
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

			RewriteUtils.deleteNodeText(rewriter, mOperandChanges.get(deleteIndex).getNode());
			RewriteUtils.replaceByWhitespace(rewriter, lhs.mOperatorPosition);
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
