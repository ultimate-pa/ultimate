/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.IInlineSelector;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel.EdgeType;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.ILabeledEdgesFilter;

/**
 * Selector using the preferences from the BoogieProcedureInliner.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class PreferencesInlineSelector implements IInlineSelector {
	
	private boolean mInlineUnimplemented;
	private boolean mInlineImplemented;
	private boolean mIgnoreCallForAll;
	private boolean mIgnoreRecursive;
	private boolean mIgnoreWithFreeRequires;
	private boolean mIgnorePolymorphic;
	private boolean mIgnoreMultipleCalled;
	private Collection<String> mUserList;
	private UserListType mUserListType;

	/**
	 * Mapping from procedure id, to the last processed edge, which's inlineFlag was set.
	 * This is used to undo the possibly wrong assumption "every procedure is only called once".
	 */
	private Map<String, CallGraphEdgeLabel> mLastInlinedCall;
	
	/** Creates a new InlineSelector using the currently set preferences of the BoogieProcedureInliner. */
	public PreferencesInlineSelector() {
		mInlineUnimplemented = PreferenceItem.INLINE_UNIMPLEMENTED.getBooleanValue();
		mInlineImplemented = PreferenceItem.INLINE_IMPLEMENTED.getBooleanValue();
		mIgnoreCallForAll = PreferenceItem.IGNORE_CALL_FORALL.getBooleanValue();
		mUserList = new HashSet<String>(PreferenceItem.USER_LIST.getStringValueTokens());
		mUserListType = PreferenceItem.USER_LIST_TYPE.getUserListTypeValue();
		mIgnoreRecursive = PreferenceItem.IGNORE_RECURSIVE.getBooleanValue();
		mIgnoreWithFreeRequires = PreferenceItem.IGNORE_WITH_FREE_REQUIRES.getBooleanValue();
		mIgnorePolymorphic = PreferenceItem.IGNORE_MULTIPLE_CALLED.getBooleanValue();
		mIgnoreMultipleCalled = PreferenceItem.IGNORE_MULTIPLE_CALLED.getBooleanValue();
	}

	@Override
	public void setInlineFlags(Map<String, CallGraphNode> callGraph) {
		mLastInlinedCall = new HashMap<String, CallGraphEdgeLabel>();
		List<ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel>> updaterQueue = new ArrayList<>(2);
		if (!mUserListType.isOnly()) {
			updaterQueue.add(mGeneralSettingsFilter);
		}
		if (mUserListType != UserListType.DISABLED) {
			updaterQueue.add(mUserListFilter);			
		}
		for (ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> filter : updaterQueue) {	
			for (CallGraphNode caller : callGraph.values()) {
				Iterator<CallGraphEdgeLabel> outgoingEdgeLabelsIterator = caller.getOutgoingEdgeLabels().iterator();
				Iterator<CallGraphNode> outgoingNodesIterator = caller.getOutgoingNodes().iterator();
				while (outgoingEdgeLabelsIterator.hasNext() && outgoingNodesIterator.hasNext()) {
					CallGraphEdgeLabel callLabel = outgoingEdgeLabelsIterator.next();
					CallGraphNode callee = outgoingNodesIterator.next();
					callLabel.setInlineFlag(filter.accept(caller, callLabel, callee));
				}
				assert outgoingEdgeLabelsIterator.hasNext() == outgoingNodesIterator.hasNext();
			}
		}
	}
	
	/** Filter determining whether to set an inline flag or not, using the general settings. */
	private ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> mGeneralSettingsFilter =
			new ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel>() {
		@Override
		public boolean accept(CallGraphNode caller, CallGraphEdgeLabel callLabel, CallGraphNode callee) {
			boolean inline;
			if (mIgnoreWithFreeRequires && hasFreeRequiresSpecification(callee)) {
				inline = false;
			} else if (mIgnorePolymorphic && (caller.isPolymorphic() || callee.isPolymorphic())) {
				inline = false;
			} else if (mIgnoreRecursive && callLabel.getEdgeType().isRecursive()) {
				inline = false;
			} else if (mIgnoreCallForAll && callLabel.getEdgeType() == EdgeType.CALL_FORALL) {
				inline = false;
			} else {
				// Assume that all procedures are called only once.
				boolean isImplemented = callee.isImplemented();
				inline = mInlineImplemented && isImplemented || mInlineUnimplemented && !isImplemented;
				if (inline && mIgnoreMultipleCalled) {
					CallGraphEdgeLabel inlinedCallOfSameProcedure = mLastInlinedCall.put(callee.getId(), callLabel);
					if (inlinedCallOfSameProcedure != null) {
						// The assumption was false. There where multiple calls => undo
						inlinedCallOfSameProcedure.setInlineFlag(false);
						inline = false;
					}
				}
			}
			return inline;
		}
	};
	
	private boolean hasFreeRequiresSpecification(CallGraphNode procNode) {
		for (Specification spec : procNode.getProcedureWithSpecification().getSpecification()) {
			if (spec instanceof RequiresSpecification && spec.isFree()) {
				return true;
			}
		}
		return false;
	}
	
	/** Filter determining whether to set an inline flag or not, using the previously set flag and the user list. */
	private ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> mUserListFilter =
			new ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel>() {
		@Override
		public boolean accept(CallGraphNode caller, CallGraphEdgeLabel callLabel, CallGraphNode callee) {
			boolean inline = callLabel.getInlineFlag();
			boolean inUserList = mUserList.contains(callee.getId());
			switch(mUserListType) {
				case BLACKLIST_ONLY:
					inline = !inUserList;
					break;
				case BLACKLIST_RESTRICT:
					inline = inline && !inUserList;
					break;
				case DISABLED:
					// nothing to do
					break;
				case WHITELIST_EXTEND:
					inline = inline || inUserList;
					break;
				case WHITELIST_ONLY:
					inline = inUserList;
					break;
				case WHITELIST_RESTRICT:
					inline = inline && inUserList;
					break;
				default:
					throw new IllegalArgumentException("Unknown user list type: " + mUserListType);
			}
			return inline;
		}
	};
}
