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

public class DeleteWithCommaChange extends Change {
	class CombinedChange extends Change {
		List<IPSTNode> childrenToDelete = new ArrayList<>();

		CombinedChange(final IPSTNode node) {
			super(node);
		}

		void addChild(final IPSTNode child) {
			childrenToDelete.add(child);
		}

		@Override
		public void apply(final SourceRewriter rewriter) {
			// Just sort the nodes instead of relying that they are already
			// in order (which should be the case, though)
			childrenToDelete.sort(HierarchicalSourceRangeComparator.getInstance());

			if (keepOne && commaPositions.size() - childrenToDelete.size() < 1) {
				throw new ChangeConflictException("Applying this combination of changes would delete the last element");
			}

			CommaDeleter.deleteNodesWithComma(rewriter, childrenToDelete, commaPositions);
		}
	}

	IPSTNode parent;
	List<CommaSeparatedChild> commaPositions;

	boolean keepOne;

	public DeleteWithCommaChange(final IPSTRegularNode node, final IPSTRegularNode parent,
			final List<CommaSeparatedChild> commaPositions, final boolean keepOne) {
		super(node);
		this.parent = parent;
		this.commaPositions = commaPositions;
		this.keepOne = keepOne;
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
		return "Delete with comma " + getNode() + " (from " + parent + ")";
	}

	@Override
	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(parent, CombinedChange::new)).addChild(getNode());
	}
}