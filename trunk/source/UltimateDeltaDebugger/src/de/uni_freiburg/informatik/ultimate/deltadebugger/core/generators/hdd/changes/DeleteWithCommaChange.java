package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChild;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.HierarchicalSourceRangeComparator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by deletion with comma.
 */
public class DeleteWithCommaChange extends Change {
	private final IPSTNode mParent;
	private final List<CommaSeparatedChild> mCommaPositions;
	
	private final boolean mKeepOne;
	
	/**
	 * @param node
	 *            PST node.
	 * @param parent
	 *            parent PST node
	 * @param commaPositions
	 *            comma positions
	 * @param keepOne
	 *            {@code true} iff one element should be kept
	 */
	public DeleteWithCommaChange(final IPSTRegularNode node, final IPSTRegularNode parent,
			final List<CommaSeparatedChild> commaPositions, final boolean keepOne) {
		super(node);
		mParent = parent;
		mCommaPositions = commaPositions;
		mKeepOne = keepOne;
	}
	
	@Override
	public void apply(final SourceRewriter rewriter) {
		// no immediate modification possible, because we need to know all nodes
		// to be delete to know how commas are deleted (to handle cases where
		// commas are missing in non-preprocessed code)
	}
	
	@Override
	public boolean hasDeferredChange() {
		return true;
	}
	
	@Override
	public String toString() {
		return "Delete with comma " + getNode() + " (from " + mParent + ")";
	}
	
	@Override
	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(mParent, CombinedChange::new)).addChild(getNode());
	}
	
	/**
	 * Combined change.
	 */
	class CombinedChange extends Change {
		private final List<IPSTNode> mChildrenToDelete = new ArrayList<>();
		
		CombinedChange(final IPSTNode node) {
			super(node);
		}
		
		void addChild(final IPSTNode child) {
			mChildrenToDelete.add(child);
		}
		
		@Override
		public void apply(final SourceRewriter rewriter) {
			// Just sort the nodes instead of relying that they are already
			// in order (which should be the case, though)
			mChildrenToDelete.sort(HierarchicalSourceRangeComparator.getInstance());
			
			if (mKeepOne && mCommaPositions.size() - mChildrenToDelete.size() < 1) {
				throw new ChangeConflictException("Applying this combination of changes would delete the last element");
			}
			
			CommaDeleter.deleteNodesWithComma(rewriter, mChildrenToDelete, mCommaPositions);
		}
	}
}
