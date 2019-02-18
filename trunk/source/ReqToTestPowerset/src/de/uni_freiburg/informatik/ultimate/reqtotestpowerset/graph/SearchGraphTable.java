package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import java.util.List;

public class SearchGraphTable {
	private final Script mScript;
	private final ILogger mLogger;
	private int mNrOfFoundTests;
	private int mNrOfFinalStates;
	
	private Map<GuardGraph, TableElement> mElements;
	
	public SearchGraphTable(ILogger logger, Script script) {
		mLogger = logger;
		mScript = script;
		mElements = new HashMap<>();
		mNrOfFoundTests = 0;
		mNrOfFinalStates = 0;
	}
	
	public void makeTests() {
		for ( GuardGraph key : mElements.keySet() ) {
			TableElement tEle = mElements.get(key);
			if ( tEle.getFinalFlag() ) {
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
	
	public String makePath(TableElement tElement) {
		if ( (tElement.getParent() == null )) {
			return null;
		}
		List<Term> result = new ArrayList<>();

		GuardGraph pnode = tElement.getParent();
		GuardGraph node = tElement.getNodeId();
		while (pnode != null) {
			result.add(pnode.getOutgoingEdgeLabel(node));
			node = mElements.get(pnode).getNodeId();
			pnode = mElements.get(node).getParent();
		}
		
		return makeStringFromArray(result);
	}
	
	private String makeStringFromArray(List<Term> list) {
		StringBuilder result = new StringBuilder();
		result.append("Found Tests: \n");
		List<Term> localList = new ArrayList<>(list);
		Collections.reverse(localList);
		for ( Term t : localList) {
			result.append(t);
			result.append("\n");
		}
		return result.toString();
	}

	public String toString() {
		StringBuilder result = new StringBuilder();
		for (GuardGraph key : mElements.keySet()) {
			result.append(mElements.get(key).toString());
			result.append("\n");
		}
		return result.toString();
	}
	
	public boolean add(GuardGraph node, int distance, GuardGraph parentNode, boolean isEndNode) {
		final TableElement localElement = new TableElement(node, distance, parentNode, isEndNode);
		
		if ( !mElements.containsKey(localElement.getNodeId()) ) {
			mElements.put(localElement.getNodeId(), localElement);
			return true;
		} else {
			return false;
		}
	}
	
	public int getDistOfElement(GuardGraph g) {
		if(mElements.containsKey(g)) {
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
		
		public TableElement(GuardGraph node, int distance, GuardGraph fromNode, boolean isEndNode) {
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
		
		public String toString() {
			StringBuilder result = new StringBuilder();
			StringBuilder noParent = new StringBuilder();
			if ( getParent() == null ) {
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
