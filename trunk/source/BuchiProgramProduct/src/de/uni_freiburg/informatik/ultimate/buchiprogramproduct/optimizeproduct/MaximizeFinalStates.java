package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class MaximizeFinalStates extends BaseProductOptimizer {

	private int mNewAcceptingStates;

	public MaximizeFinalStates(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
		mLogger.info(mNewAcceptingStates + " new accepting states");
	}

	@Override
	protected void init(RootNode root, IUltimateServiceProvider services) {
		mNewAcceptingStates = 0;
	}

	@Override
	protected RootNode process(RootNode root) {
		int lastRun = processInternal(root);
		mNewAcceptingStates += lastRun;
		while (lastRun > 0) {
			lastRun = processInternal(root);
			mNewAcceptingStates += lastRun;
		}
		return root;
	}

	private int processInternal(RootNode root) {
		ArrayDeque<ProgramPoint> nodes = new ArrayDeque<>();
		HashSet<ProgramPoint> closed = new HashSet<>();
		BuchiProgramAcceptingStateAnnotation annot = null;
		int newAcceptingStates = 0;
		for (RCFGEdge edge : root.getOutgoingEdges()) {
			nodes.add((ProgramPoint) edge.getTarget());
		}

		while (!nodes.isEmpty()) {
			ProgramPoint current = nodes.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			annot = BuchiProgramAcceptingStateAnnotation.getAnnotation(current);
			if (annot != null) {
				// this state is already accepting
				nodes.addAll(getSuccessors(current));
				continue;
			}

			List<ProgramPoint> succs = getSuccessors(current);
			if (succs.isEmpty()) {
				// there are no successors
				continue;
			}

			boolean allSuccessorsAreAccepting = true;
			for (ProgramPoint succ : succs) {
				annot = BuchiProgramAcceptingStateAnnotation.getAnnotation(succ);
				allSuccessorsAreAccepting = allSuccessorsAreAccepting && annot != null;
				nodes.add(succ);
			}

			if (allSuccessorsAreAccepting) {
				// all successors are accepting, make this one also accepting
				annot.annotate(current);
				newAcceptingStates++;
			}

		}
		return newAcceptingStates;
	}

	public int getNewAcceptingStates() {
		return mNewAcceptingStates;
	}

	@Override
	public boolean IsGraphChanged() {
		return mNewAcceptingStates > 0;
	}
}
