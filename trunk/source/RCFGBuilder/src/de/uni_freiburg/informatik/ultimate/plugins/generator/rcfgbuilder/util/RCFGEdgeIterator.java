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

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RCFGEdgeIterator implements Iterator<IcfgEdge> {

	private final Deque<IcfgEdge> mWorklist;
	private final Set<IcfgEdge> mFinished;

//	public RCFGEdgeIterator(final RootNode root) {
//		this(root.getOutgoingEdges());
//	}

	public <T extends IcfgEdge> RCFGEdgeIterator(final Collection<T> edges) {
		mFinished = new HashSet<>();
		mWorklist = new ArrayDeque<>();
		mWorklist.addAll(edges);
	}

	@Override
	public boolean hasNext() {
		return !mWorklist.isEmpty();
	}

	@Override
	public IcfgEdge next() {
		final IcfgEdge current = mWorklist.removeFirst();
		final IcfgLocation target = current.getTarget();
		if (target == null) {
			assert false : "Dangling edge";
			return current;
		}
		target.getOutgoingEdges().stream().filter(mFinished::add).forEachOrdered(mWorklist::add);
		return current;
	}

	public Stream<IcfgEdge> asStream() {
		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(this, Spliterator.ORDERED), false);
	}
}
