package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RCFGEdgeIterator implements Iterator<RCFGEdge> {

	private final Deque<RCFGEdge> mWorklist;
	private final Set<RCFGEdge> mFinished;

	public RCFGEdgeIterator(final RootNode root) {
		this(root.getOutgoingEdges());
	}

	public <T extends RCFGEdge> RCFGEdgeIterator(final Collection<T> edges) {
		mFinished = new HashSet<>();
		mWorklist = new ArrayDeque<>();
		mWorklist.addAll(edges);
	}

	@Override
	public boolean hasNext() {
		return !mWorklist.isEmpty();
	}

	@Override
	public RCFGEdge next() {
		final RCFGEdge current = mWorklist.removeFirst();
		final RCFGNode target = current.getTarget();
		if (target == null) {
			assert false : "Dangling edge";
			return current;
		}
		target.getOutgoingEdges().stream().filter(mFinished::add).forEachOrdered(mWorklist::add);
		return current;
	}

	public Stream<RCFGEdge> asStream() {
		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(this, Spliterator.ORDERED), false);
	}
}
