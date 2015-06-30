package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.Comparator;
import java.util.HashSet;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.Utils;

class FasterPriorityQueue<EDGE> {
	private final Queue<EDGE> mOpen;
	private final Set<EDGE> mOpenSupport;

	FasterPriorityQueue(Comparator<EDGE> comp) {
		mOpen = new PriorityQueue<>(10, comp);
		mOpenSupport = new HashSet<EDGE>();
	}

	public void remove(EDGE successor) {
		mOpen.remove(successor);
		mOpenSupport.remove(successor);

	}

	public EDGE poll() {
		final EDGE rtr = mOpen.poll();
		mOpenSupport.remove(rtr);
		return rtr;
	}

	public boolean isEmpty() {
		return mOpen.isEmpty();
	}

	public void add(EDGE nodeDecorator) {
		mOpen.add(nodeDecorator);
		mOpenSupport.add(nodeDecorator);
	}

	public boolean contains(EDGE obj) {
		return mOpenSupport.contains(obj);
	}

	@Override
	public String toString() {
		return Utils.join(mOpen, ", ");
	}
}