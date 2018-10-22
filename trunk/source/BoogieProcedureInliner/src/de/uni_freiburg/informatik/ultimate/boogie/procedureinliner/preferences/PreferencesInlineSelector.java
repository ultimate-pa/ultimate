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
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.IInlineSelector;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel.EdgeType;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter.ILabeledEdgesFilter;

/**
 * Selector using the preferences from the BoogieProcedureInliner.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class PreferencesInlineSelector implements IInlineSelector {

	private final boolean mInlineUnimplemented;
	private final boolean mInlineImplemented;
	private final boolean mIgnoreCallForAll;
	private final boolean mIgnoreRecursive;
	private final boolean mIgnoreWithFreeRequires;
	private final boolean mIgnorePolymorphic;
	private final boolean mIgnoreMultipleCalled;
	private final Collection<String> mUserList;
	private final UserListType mUserListType;

	/** Filter determining whether to set an inline flag or not, using the general settings. */
	private final ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> mGeneralSettingsFilter;

	/** Filter determining whether to set an inline flag or not, using the previously set flag and the user list. */
	private final ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> mUserListFilter;

	/**
	 * Mapping from procedure id, to the last processed edge, which's inlineFlag was set. This is used to undo the
	 * possibly wrong assumption "every procedure is only called once".
	 */
	private Map<String, CallGraphEdgeLabel> mLastInlinedCall;

	/**
	 * Creates a new InlineSelector using the currently set preferences of the BoogieProcedureInliner.
	 *
	 * @param services
	 *            The current {@link IUltimateServiceProvider} instance that is used to retrieve valid preferences.
	 */
	public PreferencesInlineSelector(final IUltimateServiceProvider services) {
		mInlineUnimplemented = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceItem.INLINE_UNIMPLEMENTED.getName());
		mInlineImplemented = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceItem.INLINE_IMPLEMENTED.getName());
		mIgnoreCallForAll = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceItem.IGNORE_CALL_FORALL.getName());
		mUserList = new HashSet<>(PreferenceItem.USER_LIST.getStringValueTokens(services));
		mUserListType = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(PreferenceItem.USER_LIST_TYPE.getName(), UserListType.class);
		mIgnoreRecursive = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceItem.IGNORE_RECURSIVE.getName());
		mIgnoreWithFreeRequires = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceItem.IGNORE_WITH_FREE_REQUIRES.getName());
		mIgnorePolymorphic = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceItem.IGNORE_MULTIPLE_CALLED.getName());
		mIgnoreMultipleCalled = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceItem.IGNORE_MULTIPLE_CALLED.getName());
		mGeneralSettingsFilter = new GeneralSettingsFilter();
		mUserListFilter = new UserListFilter();
	}

	@Override
	public void setInlineFlags(final Map<String, CallGraphNode> callGraph) {
		mLastInlinedCall = new HashMap<>();
		final List<ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel>> updaterQueue = new ArrayList<>(2);
		if (!mUserListType.isOnly()) {
			updaterQueue.add(mGeneralSettingsFilter);
		}
		if (mUserListType != UserListType.DISABLED) {
			updaterQueue.add(mUserListFilter);
		}
		for (final ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> filter : updaterQueue) {
			for (final CallGraphNode caller : callGraph.values()) {
				final Iterator<CallGraphEdgeLabel> outgoingEdgeLabelsIterator =
						caller.getOutgoingEdgeLabels().iterator();
				final Iterator<CallGraphNode> outgoingNodesIterator = caller.getOutgoingNodes().iterator();
				while (outgoingEdgeLabelsIterator.hasNext() && outgoingNodesIterator.hasNext()) {
					final CallGraphEdgeLabel callLabel = outgoingEdgeLabelsIterator.next();
					final CallGraphNode callee = outgoingNodesIterator.next();
					callLabel.setInlineFlag(filter.accept(caller, callLabel, callee));
				}
				assert outgoingEdgeLabelsIterator.hasNext() == outgoingNodesIterator.hasNext();
			}
		}
	}

	private final class UserListFilter implements ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> {
		@Override
		public boolean accept(final CallGraphNode caller, final CallGraphEdgeLabel callLabel,
				final CallGraphNode callee) {
			final boolean inline = callLabel.getInlineFlag();
			final boolean inUserList = mUserList.contains(callee.getId());
			switch (mUserListType) {
			case BLACKLIST_ONLY:
				return !inUserList;
			case BLACKLIST_RESTRICT:
				return inline && !inUserList;
			case DISABLED:
				return inline;
			case WHITELIST_EXTEND:
				return inline || inUserList;
			case WHITELIST_ONLY:
				return inUserList;
			case WHITELIST_RESTRICT:
				return inline && inUserList;
			default:
				throw new IllegalArgumentException("Unknown user list type: " + mUserListType);
			}
		}
	}

	private final class GeneralSettingsFilter implements ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> {
		@Override
		public boolean accept(final CallGraphNode caller, final CallGraphEdgeLabel callLabel,
				final CallGraphNode callee) {
			if (mIgnoreWithFreeRequires && hasFreeRequiresSpecification(callee)) {
				return false;
			} else if (mIgnorePolymorphic && (caller.isPolymorphic() || callee.isPolymorphic())) {
				return false;
			} else if (mIgnoreRecursive && callLabel.getEdgeType().isRecursive()) {
				return false;
			} else if (mIgnoreCallForAll && callLabel.getEdgeType() == EdgeType.CALL_FORALL) {
				return false;
			} else if (callLabel.getEdgeType() == EdgeType.FORK) {
				return false;
			} else {
				return acceptNormalCall(callLabel, callee);
			}
		}

		private boolean acceptNormalCall(final CallGraphEdgeLabel callLabel, final CallGraphNode callee) {
			// Assume that all procedures are called only once (can be undone later)
			final boolean isImplemented = callee.isImplemented();
			final boolean inlineIfSingleCall =
					(mInlineImplemented && isImplemented) || (mInlineUnimplemented && !isImplemented);
			if (!inlineIfSingleCall || !mIgnoreMultipleCalled) {
				return inlineIfSingleCall;
			}
			final CallGraphEdgeLabel inlinedCallOfSameProcedure = mLastInlinedCall.put(callee.getId(), callLabel);
			if (inlinedCallOfSameProcedure != null) {
				// The assumption was false. There where multiple calls => undo
				inlinedCallOfSameProcedure.setInlineFlag(false);
				return false;
			}
			return true;
		}

		private boolean hasFreeRequiresSpecification(final CallGraphNode procNode) {
			for (final Specification spec : procNode.getProcedureWithSpecification().getSpecification()) {
				if (spec instanceof RequiresSpecification && spec.isFree()) {
					return true;
				}
			}
			return false;
		}
	}
}
