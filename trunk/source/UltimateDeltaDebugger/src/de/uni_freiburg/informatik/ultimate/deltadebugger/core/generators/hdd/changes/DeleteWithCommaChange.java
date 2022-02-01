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

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.CommaDeleter;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.HddChange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChild;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.HierarchicalSourceRangeComparator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by deletion with comma.
 */
public class DeleteWithCommaChange extends HddChange {
	private final IPSTNode mParent;
	private final List<CommaSeparatedChild> mCommaPositions;
	private final ISourceRange mNodeLocation;
	
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
		mNodeLocation = node;
		mKeepOne = keepOne;
	}
	
	/**
	 * Constructor to delete by location (used to delete the varargs ellipsis token).
	 * 
	 * @param parent
	 *            parent PST node
	 * @param commaPositions
	 *            comma positions
	 * @param keepOne
	 *            {@code true} iff one element should be kept
	 * @param nodeLocation
	 *            varargs token location
	 */
	public DeleteWithCommaChange(final IPSTRegularNode parent, final List<CommaSeparatedChild> commaPositions,
			final boolean keepOne, final ISourceRange nodeLocation) {
		super(parent);
		mParent = parent;
		mCommaPositions = commaPositions;
		mNodeLocation = nodeLocation;
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
		return "Delete with comma " + mNodeLocation + " (from " + mParent + ")";
	}
	
	@Override
	public void updateDeferredChange(final Map<IPSTNode, HddChange> deferredChangeMap) {
		((CombinedChange) deferredChangeMap.computeIfAbsent(mParent, CombinedChange::new))
				.addChildLocation(mNodeLocation);
	}

	/**
	 * Combined change.
	 */
	class CombinedChange extends HddChange {
		private final List<ISourceRange> mChildLocationsToDelete = new ArrayList<>();

		CombinedChange(final IPSTNode node) {
			super(node);
		}

		void addChildLocation(final ISourceRange child) {
			mChildLocationsToDelete.add(child);
		}

		@Override
		public void apply(final SourceRewriter rewriter) {
			// Just sort the nodes instead of relying that they are already
			// in order (which should be the case, though)
			mChildLocationsToDelete.sort(HierarchicalSourceRangeComparator.getInstance());

			if (mKeepOne && mCommaPositions.size() - mChildLocationsToDelete.size() < 1) {
				throw new ChangeConflictException("Applying this combination of changes would delete the last element");
			}

			CommaDeleter.deleteNodesWithComma(rewriter, mChildLocationsToDelete, mCommaPositions);
		}
	}
}
