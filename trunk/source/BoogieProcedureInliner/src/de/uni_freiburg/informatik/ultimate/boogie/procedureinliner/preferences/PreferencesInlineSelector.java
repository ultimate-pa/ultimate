package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.IInlineSelector;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel.EdgeType;

/**
 * Selector using the preferences from the BoogieProcedureInliner.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class PreferencesInlineSelector implements IInlineSelector {

	private boolean mInlineUnimplemented;
	private boolean mInlineImplemented;
	private boolean mSingleCallsOnly;
	private boolean mInlineCallForAll;
	private Collection<String> mUserList;
	private UserListType mUserListType;
	
	/**
	 * Mapping from procedure id, to the last processed edge, which's inlineFlag was set.
	 * This is used to undo the possibly wrong assumption "every call is a single call".
	 */
	private Map<String, CallGraphEdgeLabel> mLastInlinedCall;
	
	/** Creates a new InlineSelector using the currently set preferences of the BoogieProcedureInliner. */
	public PreferencesInlineSelector() {
		mInlineUnimplemented = PreferenceItem.INLINE_UNIMPLEMENTED.getBooleanValue();
		mInlineImplemented = PreferenceItem.INLINE_IMPLEMENTED.getBooleanValue();
		mSingleCallsOnly = PreferenceItem.INLINE_SINGLE_CALLS_ONLY.getBooleanValue();
		mInlineCallForAll = PreferenceItem.INLINE_CALL_FORALL.getBooleanValue();
		mUserList = new HashSet<String>(Arrays.asList(PreferenceItem.USER_LIST.getStringValue().trim().split("\\s+")));
		mUserListType = PreferenceItem.USER_LIST_TYPE.getUserListTypeValue();
	}

	@Override
	public void setInlineFlags(Map<String, CallGraphNode> callGraph) {
		mLastInlinedCall = new HashMap<String, CallGraphEdgeLabel>();
		
		for (CallGraphNode caller : callGraph.values()) {
			Iterator<CallGraphEdgeLabel> outgoingEdgeLabelsIterator = caller.getOutgoingEdgeLabels().iterator();
			Iterator<CallGraphNode> outgoingNodesIterator = caller.getOutgoingNodes().iterator();
			while (outgoingEdgeLabelsIterator.hasNext() && outgoingNodesIterator.hasNext()) {
				CallGraphEdgeLabel callLabel = outgoingEdgeLabelsIterator.next();
				CallGraphNode callee = outgoingNodesIterator.next();
				setInlineFlag(callLabel, callee);
			}
		}
	}

	private void setInlineFlag(CallGraphEdgeLabel callLabel, CallGraphNode callee) {
		boolean inline;
		if (callLabel.getEdgeType().isRecursive()) {
			inline = false;
		} else if (callLabel.getEdgeType() == EdgeType.CALL_FORALL) {
			inline = mInlineCallForAll;
		} else if (mUserListType == UserListType.WHITELIST_ONLY) {
			inline = mUserList.contains(callee.getId());
		} else if (mUserListType == UserListType.BLACKLIST_ONLY) {
			inline = !mUserList.contains(callee.getId());
		} else {
			inline = (mInlineImplemented && callee.isImplemented())
					|| (mInlineUnimplemented && !callee.isImplemented());
			if (inline && mSingleCallsOnly) {
				CallGraphEdgeLabel inlinedCallOfSameProcedure = mLastInlinedCall.put(callee.getId(), callLabel);
				if (inlinedCallOfSameProcedure != null) {
					boolean correctedFlag = mUserListType == UserListType.WHITELIST_EXTEND
							&& mUserList.contains(callee.getId());
					inlinedCallOfSameProcedure.setInlineFlag(correctedFlag); // undo already set flag						
					inline = false; // not a "single call"
				}
			}
			if (mUserListType == UserListType.WHITELIST_EXTEND) {
				inline = inline || mUserList.contains(callee.getId());				
			} else if (mUserListType == UserListType.WHITELIST_RESTRICT) {
				inline = inline && mUserList.contains(callee.getId());				
			} else if (mUserListType == UserListType.BLACKLIST_RESTRICT) {
				inline = inline && !mUserList.contains(callee.getId());			
			}
			callLabel.setInlineFlag(inline);
		}
	}

}
