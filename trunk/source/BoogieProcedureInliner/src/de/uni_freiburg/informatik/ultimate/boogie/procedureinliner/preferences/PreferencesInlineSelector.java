package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

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
	private boolean mInlineCallForAll;
	private boolean mIgnoreRecursive;
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
		mInlineCallForAll = PreferenceItem.INLINE_CALL_FORALL.getBooleanValue();
		mUserList = new HashSet<String>(Arrays.asList(PreferenceItem.USER_LIST.getStringValue().trim().split("\\s+")));
		mUserListType = PreferenceItem.USER_LIST_TYPE.getUserListTypeValue();
		mIgnoreRecursive = PreferenceItem.IGNORE_RECURSIVE.getBooleanValue();
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
			if (mIgnorePolymorphic && (caller.isPolymorphic() || callee.isPolymorphic())) {
				inline = false;
			} else if (mIgnoreRecursive && callLabel.getEdgeType().isRecursive()) {
				inline = false;
			} else if (mInlineCallForAll && callLabel.getEdgeType() == EdgeType.CALL_FORALL) {
				inline = true;
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
			}
			return inline;
		}
	};
}
