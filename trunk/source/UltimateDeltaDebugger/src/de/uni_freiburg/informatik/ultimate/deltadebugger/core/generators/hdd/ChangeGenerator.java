package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.Change;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.ChangeCollector;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChild;

class ChangeGenerator {
	
	protected final HDDStrategy strategy;
	private final Map<IPSTRegularNode, List<CommaSeparatedChild>> parentToCommaPositionMap = new IdentityHashMap<>();
	
	public ChangeGenerator(HDDStrategy strategy) {
		this.strategy = strategy;
	}
	
	
	static class ExpansionResult {
		final int advancedLevels;
		final List<List<Change>> changeGroups;
		final List<IPSTNode> remainingNodes;
		
		public ExpansionResult(int advancedLevels, List<List<Change>> changeGroups, List<IPSTNode> remainingNodes) {
			this.advancedLevels = advancedLevels;
			this.changeGroups = changeGroups;
			this.remainingNodes = remainingNodes;
		}
	}
	
	ExpansionResult generateNextLevelChanges(List<IPSTNode> currentLevelNodes) {
		int advancedLevels = 0;
		// A certain level may not generate a change but still contain nodes to expand, 
		// so loop until either some changes are generated or no nodes remain
		List<List<Change>> changeGroups = Collections.emptyList();
		List<IPSTNode> remainingNodes = currentLevelNodes;
		while(changeGroups.isEmpty() && !remainingNodes.isEmpty()) {
			final List<IPSTNode> nextLevelNodes = new ArrayList<>();
			changeGroups = expandCurrentLevel(remainingNodes, nextLevelNodes);
			remainingNodes = nextLevelNodes;
			++advancedLevels;
		}
		
		return new ExpansionResult(advancedLevels, changeGroups, remainingNodes);
	}
	
	
	List<List<Change>> expandCurrentLevel(List<IPSTNode> remaingNodesOnCurrentLevel, List<IPSTNode> nextLevelNodes) {
		final List<List<Change>> changeGroups = new ArrayList<>();
		
		final ChangeCollector collector = new ChangeCollector(parentToCommaPositionMap);
		for (IPSTNode node : remaingNodesOnCurrentLevel) {
			if (strategy.expandIntoOwnGroup(node)) {
				final ChangeCollector subcollector = new ChangeCollector(parentToCommaPositionMap);
				expandCurrentLevelNode(node, nextLevelNodes, subcollector);
				if (!subcollector.getChanges().isEmpty()) {
					changeGroups.add(subcollector.getChanges());
				}
			} else {
				expandCurrentLevelNode(node, nextLevelNodes, collector);
			}
		}
		if (!collector.getChanges().isEmpty()) {
			changeGroups.add(collector.getChanges());
		}
		
		return changeGroups;
	}
	
	
	
	
	
	private void expandCurrentLevelNode(IPSTNode node, List<IPSTNode> nextLevelNodes, ChangeCollector collector) {
		strategy.createAdditionalChangesForExpandedNode(node, collector);
		for (IPSTNode child : node.getChildren()) {
			if (strategy.skipSubTree(child)) {
				continue;
			}
			final int previousChangeCount = collector.getChanges().size();
			strategy.createChangeForNode(child, collector);
			if (previousChangeCount == collector.getChanges().size()
					&& strategy.expandUnchangeableNodeImmediately(child) && !strategy.expandIntoOwnGroup(child)) {
				expandCurrentLevelNode(child, nextLevelNodes, collector);
			} else {
				nextLevelNodes.add(child);
			}
		}
	}
}

