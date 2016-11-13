package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.Change;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.ChangeCollector;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChild;

/**
 * Generator of changes in the C file.
 */
class ChangeGenerator {
	private final ILogger mLogger;
	private final IHddStrategy mStrategy;
	
	private final Map<IPSTRegularNode, List<CommaSeparatedChild>> mParentToCommaPositionMap = new IdentityHashMap<>();
	
	public ChangeGenerator(final ILogger logger, final IHddStrategy strategy) {
		mLogger = logger;
		mStrategy = strategy;
	}
	
	private List<List<Change>> expandCurrentLevel(final List<IPSTNode> remaingNodesOnCurrentLevel,
			final List<IPSTNode> nextLevelNodes) {
		final List<List<Change>> changeGroups = new ArrayList<>();
		
		final ChangeCollector collector = new ChangeCollector(mLogger, mParentToCommaPositionMap);
		for (final IPSTNode node : remaingNodesOnCurrentLevel) {
			if (mStrategy.expandIntoOwnGroup(node)) {
				final ChangeCollector subcollector = new ChangeCollector(mLogger, mParentToCommaPositionMap);
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
	
	private void expandCurrentLevelNode(final IPSTNode node, final List<IPSTNode> nextLevelNodes,
			final ChangeCollector collector) {
		mStrategy.createAdditionalChangesForExpandedNode(node, collector);
		for (final IPSTNode child : node.getChildren()) {
			if (mStrategy.skipSubTree(child)) {
				continue;
			}
			final int previousChangeCount = collector.getChanges().size();
			mStrategy.createChangeForNode(child, collector);
			if (previousChangeCount == collector.getChanges().size()
					&& mStrategy.expandUnchangeableNodeImmediately(child) && !mStrategy.expandIntoOwnGroup(child)) {
				expandCurrentLevelNode(child, nextLevelNodes, collector);
			} else {
				nextLevelNodes.add(child);
			}
		}
	}
	
	ExpansionResult generateNextLevelChanges(final List<IPSTNode> currentLevelNodes) {
		int advancedLevels = 0;
		// A certain level may not generate a change but still contain nodes to expand,
		// so loop until either some changes are generated or no nodes remain
		List<List<Change>> changeGroups = Collections.emptyList();
		List<IPSTNode> remainingNodes = currentLevelNodes;
		while (changeGroups.isEmpty() && !remainingNodes.isEmpty()) {
			final List<IPSTNode> nextLevelNodes = new ArrayList<>();
			changeGroups = expandCurrentLevel(remainingNodes, nextLevelNodes);
			remainingNodes = nextLevelNodes;
			++advancedLevels;
		}
		
		return new ExpansionResult(advancedLevels, changeGroups, remainingNodes);
	}
	
	/**
	 * Expansion result.
	 */
	static class ExpansionResult {
		protected final int mAdvancedLevels;
		protected final List<List<Change>> mChangeGroups;
		protected final List<IPSTNode> mRemainingNodes;
		
		public ExpansionResult(final int advancedLevels, final List<List<Change>> changeGroups,
				final List<IPSTNode> remainingNodes) {
			mAdvancedLevels = advancedLevels;
			mChangeGroups = changeGroups;
			mRemainingNodes = remainingNodes;
		}
	}
}
