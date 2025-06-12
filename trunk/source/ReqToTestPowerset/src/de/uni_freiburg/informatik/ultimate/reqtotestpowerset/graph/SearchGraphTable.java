package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class SearchGraphTable {
	private final Script mScript;
	private final ILogger mLogger;
	private int mNrOfFoundTests;
	private int mNrOfFinalStates;

	private final Map<GuardGraph, TableElement> mElements;

	public SearchGraphTable(final ILogger logger, final Script script) {
		mLogger = logger;
		mScript = script;
		mElements = new HashMap<>();
		mNrOfFoundTests = 0;
		mNrOfFinalStates = 0;
	}

	public void makeTests() {
		for (final GuardGraph key : mElements.keySet()) {
			final TableElement tEle = mElements.get(key);
			if (tEle.getFinalFlag()) {
				mNrOfFinalStates++;
				mNrOfFoundTests += tEle.getNodeId().getOutgoingNodes().size();
			}
		}
	}

	public int getNrOfTests() {
		return mNrOfFoundTests;
	}

	public int getNrOfFinals() {
		return mNrOfFinalStates;
	}

	public String makePath(final TableElement tElement) {
		if ((tElement.getParent() == null)) {
			return null;
		}
		final List<Term> result = new ArrayList<>();

		GuardGraph pnode = tElement.getParent();
		GuardGraph node = tElement.getNodeId();
		while (pnode != null) {
			result.add(pnode.getOutgoingEdgeLabel(node));
			node = mElements.get(pnode).getNodeId();
			pnode = mElements.get(node).getParent();
		}

		return makeStringFromArray(result);
	}

	private String makeStringFromArray(final List<Term> list) {
		final StringBuilder result = new StringBuilder();
		result.append("Found Tests: \n");
		final List<Term> localList = new ArrayList<>(list);
		Collections.reverse(localList);
		for (final Term t : localList) {
			result.append(t);
			result.append("\n");
		}
		return result.toString();
	}

	@Override
	public String toString() {
		final StringBuilder result = new StringBuilder();
		for (final GuardGraph key : mElements.keySet()) {
			result.append(mElements.get(key).toString());
			result.append("\n");
		}
		return result.toString();
	}

	public boolean add(final GuardGraph node, final int distance, final GuardGraph parentNode,
			final boolean isEndNode) {
		final TableElement localElement = new TableElement(node, distance, parentNode, isEndNode);

		if (!mElements.containsKey(localElement.getNodeId())) {
			mElements.put(localElement.getNodeId(), localElement);
			return true;
		} else {
			return false;
		}
	}

	public int getDistOfElement(final GuardGraph g) {
		if (mElements.containsKey(g)) {
			return mElements.get(g).getDistance();
		} else {
			return 1;
		}
	}

	public class TableElement {

		private final GuardGraph mNodeId;
		private final int mDist;
		private final GuardGraph mParentNode;
		private final boolean mIsFinal;

		public TableElement(final GuardGraph node, final int distance, final GuardGraph fromNode,
				final boolean isEndNode) {
			mNodeId = node;
			mDist = distance;
			mParentNode = fromNode;
			mIsFinal = isEndNode;

		}

		public int getDistance() {
			return mDist;
		}

		public GuardGraph getParent() {
			return mParentNode;
		}

		public boolean getFinalFlag() {
			return mIsFinal;
		}

		public GuardGraph getNodeId() {
			return mNodeId;
		}

		@Override
		public String toString() {
			final StringBuilder result = new StringBuilder();
			final StringBuilder noParent = new StringBuilder();
			if (getParent() == null) {
				noParent.append("NONE");
			} else {
				noParent.append(getParent().getLabel());
			}
			result.append(String.format("TableTerm has id: %d, from parent %s, with distance %d, and is final %s",
					getNodeId().getLabel(), noParent.toString(), getDistance(), getFinalFlag()));

			return result.toString();
		}
	}
}
