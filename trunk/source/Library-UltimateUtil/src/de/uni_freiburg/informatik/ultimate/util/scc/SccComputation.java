/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.scc;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.CombinatoricsUtils;

/**
 * Computes strongly connected components (SCCs) of a graph. Implementation of Tarjan SCC algorithm. See
 * <a href="http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm">Wikipedia</a>.
 *
 * @param <NODE>
 *            Type of objects that represent nodes of the graph.
 * @param <COMP>
 *            Type of objects that represent strongly connected components.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class SccComputation<NODE, COMP extends StronglyConnectedComponent<NODE>> {

	private final ILogger mLogger;

	private final IStronglyConnectedComponentFactory<NODE, COMP> mSccFactory;
	protected final ISuccessorProvider<NODE> mSuccessorProvider;

	/**
	 * Number of all states to which the SCC computation is applied.
	 */
	private final int mNumberOfAllStates;
	/**
	 * Number of vertices that have been processed so far.
	 */
	protected int mIndex = 0;
	/**
	 * Vertices that have not yet been assigned to any SCC.
	 */
	protected final StackHashSet<NODE> mNoScc = new StackHashSet<>();
	/**
	 * Assigns to each vertex v the number of vertices that have been processed before in this algorithm. This number is
	 * called the index of v.
	 */
	protected final Map<NODE, Integer> mIndices = new HashMap<>();
	protected final Map<NODE, Integer> mLowLinks = new HashMap<>();
	protected final ArrayList<COMP> mBalls = new ArrayList<>();
	protected final ArrayList<COMP> mSCCs = new ArrayList<>();
	private int mNumberOfNonBallSCCs = 0;

	public SccComputation(final ILogger logger, final ISuccessorProvider<NODE> successorProvider,
			final IStronglyConnectedComponentFactory<NODE, COMP> sccFac, final int numberOfAllNodes,
			final Set<NODE> startNodes) {
		super();
		mLogger = logger;
		mSccFactory = sccFac;
		mSuccessorProvider = successorProvider;
		mNumberOfAllStates = numberOfAllNodes;

		for (final NODE node : startNodes) {
			if (!mIndices.containsKey(node)) {
				strongconnect(node);
			}
		}
		assert automatonPartitionedBySCCs();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Graph consists of " + getBalls().size() + " InCaSumBalls and " + mNumberOfNonBallSCCs
					+ " non ball SCCs. Number of states in SCCs " + mNumberOfAllStates + ".");
		}
	}

	/***
	 * Get a map of nodes to their corresponding components in the SCCs.
	 * @return
	 */
	public Map<NODE, COMP> getNodeToComponents() {
		final Map<NODE, COMP>componentOf = new HashMap<>();
		for (final COMP comp : getSCCs()) {
			for (final NODE pred : comp.getNodes()) {
				componentOf.put(pred, comp);
			}
		}
		return componentOf;
	}

	/***
	 * Get a successor provider for the SCCs.
	 *
	 * The result of this method is the projection of the input graph of this class instance to the SCCs computed by
	 * this class.
	 *
	 * I.e. let G be the input graph for this class instance, the the result of this method represents this graph:
	 *  { (scc1, scc2) | exists x, y. x in scc1, y in scc2, (x, y) in G, scc1 != scc2 }
	 *
	 * @return
	 */
	public ISuccessorProvider<COMP> getComponentsSuccessorsProvider() {

		final Map<NODE, COMP> componentOf = getNodeToComponents();
		final Map<COMP, Set<COMP>> adjComp = new HashMap<>();

		for (final COMP comp : getSCCs()) {
			if (!adjComp.containsKey(comp)) {
				adjComp.put(comp, new HashSet<>());
			}
		}
		for (final NODE source : mIndices.keySet()) {
			final COMP comp = componentOf.get(source);
			for (final NODE target : CombinatoricsUtils.iterateAll(mSuccessorProvider.getSuccessors(source))) {
				final COMP targetComp = componentOf.get(target);
				if (!comp.equals(targetComp)) {
					adjComp.get(comp).add(targetComp);
				}
			}
		}
		return new ISuccessorProvider<COMP>() {

			@Override
			public Iterator<COMP> getSuccessors(final COMP node) {
				return adjComp.get(node).iterator();
			}
		};
	}

	/***
	 * Get all components root components
	 * @return
	 */
	public Collection<COMP> getRootComponents() {
		final Set<COMP> res = new HashSet<>();
		res.addAll(getSCCs());
		final ISuccessorProvider<COMP> componentsSuccessors = getComponentsSuccessorsProvider();
		for (final COMP comp : getSCCs()) {
			for (final COMP next : CombinatoricsUtils.iterateAll(componentsSuccessors.getSuccessors(comp))) {
				res.remove(next);
			}
		}
		return res;
	}

	/***
	 * Get all the leaf components of the SCC directed-acyclic graph
	 * @return
	 */
	public Collection<COMP> getLeafComponents() {
		final ISuccessorProvider<COMP> componentsSuccessors = getComponentsSuccessorsProvider();
		final Set<COMP> res = new HashSet<>();
		for (final COMP comp : getSCCs()) {
			if (!componentsSuccessors.getSuccessors(comp).hasNext()) {
				res.add(comp);
			}
		}
		return res;
	}

	public Collection<COMP> getLeafComponents(final Iterable<NODE> root) {
		final ISuccessorProvider<COMP> componentsSuccessors = getComponentsSuccessorsProvider();
		final Set<COMP> res = new HashSet<>();
		final Stack<COMP> stk = new Stack<>();
		for (final NODE r : root) {
			stk.add(getNodeToComponents().get(r));
		}
		final Set<COMP> visited = new HashSet<>();

		while (!stk.isEmpty()) {
			final COMP top = stk.pop();
			boolean hasNext = false;
			for (final Iterator<COMP> it = componentsSuccessors.getSuccessors(top); it.hasNext(); ) {
				final COMP nxt = it.next();
				if (!visited.contains(nxt)) {
					visited.add(nxt);
					stk.add(nxt);
				}
				hasNext = true;
			}
			if (!hasNext) {
				res.add(top);
			}
		}
		return res;
	}


	public Collection<NODE> getLeafNodes() {
		final Set<NODE> res = new HashSet<>();
		for (final COMP comp : getLeafComponents()) {
			res.add(comp.getRootNode());
		}
		return res;
	}


	public Collection<NODE> getLeafNodes(final NODE root) {
		final Set<NODE> res = new HashSet<>();
		res.add(root);
		return getLeafNodes(res);
	}


	public Collection<NODE> getLeafNodes(final Iterable<NODE> root) {
		final Collection<COMP> comps = getLeafComponents(root);
		final Set<NODE> res = new HashSet<>();
		for (final COMP comp : comps) {
			res.add(comp.getRootNode());
		}
		return res;
	}
	/**
	 * @return a {@link Collection} of "ball" SCCs. A ball SCC is a SCC with at least one edge. I.e., this method
	 *         returns the subset of {@link #getSCCs()} that excludes all trivial SCCs that consist of only one vertex
	 *         that itself are disconnected.
	 */
	public Collection<COMP> getBalls() {
		return Collections.unmodifiableList(mBalls);
	}

	/**
	 * @return a list of all SCCs (ball SCCs and non-ball SCCs). If SCC a is reachable from SCC b, then SCC a occurs in
	 *         this list before SCC b (reverse topological order with respect to reachability).
	 */
	public List<COMP> getSCCs() {
		return Collections.unmodifiableList(mSCCs);
	}

	protected void strongconnect(final NODE v) {
		assert !mIndices.containsKey(v);
		assert !mLowLinks.containsKey(v);
		mIndices.put(v, mIndex);
		mLowLinks.put(v, mIndex);
		mIndex++;
		this.mNoScc.push(v);

		final Iterator<NODE> it = mSuccessorProvider.getSuccessors(v);
		while (it.hasNext()) {
			final NODE succCont = it.next();
			processSuccessor(v, succCont);
		}

		if (mLowLinks.get(v).equals(mIndices.get(v))) {
			establishNewComponent(v);
		}
	}

	protected void establishNewComponent(final NODE v) {
		NODE w;
		final COMP scc = mSccFactory.constructNewSCComponent();
		do {
			w = mNoScc.pop();
			scc.addNode(w);
		} while (v != w);
		scc.setRootNode(w);
		mSCCs.add(scc);
		if (isBall(scc)) {
			mBalls.add(scc);
		} else {
			mNumberOfNonBallSCCs++;
		}
	}

	private void processSuccessor(final NODE v, final NODE w) {
		if (!mIndices.containsKey(w)) {
			strongconnect(w);
			updateLowlink(v, mLowLinks.get(w));
		} else if (mNoScc.contains(w)) {
			updateLowlink(v, mIndices.get(w));
		}
	}

	protected void updateLowlink(final NODE node, final int newValueCandidate) {
		final int min = Math.min(mLowLinks.get(node), newValueCandidate);
		mLowLinks.put(node, min);
	}

	boolean isBall(final StronglyConnectedComponent<NODE> scc) {
		if (scc.getNumberOfStates() == 1) {
			final NODE cont = scc.getRootNode();
			final Iterator<NODE> it = mSuccessorProvider.getSuccessors(cont);
			while (it.hasNext()) {
				final NODE succCont = it.next();
				if (cont.equals(succCont)) {
					return true;
				}
			}
			return false;
		}
		assert scc.getNumberOfStates() > 1;
		return true;
	}

	/**
	 * @return true iff the SCCS form a partition of the automaton.
	 */
	protected boolean automatonPartitionedBySCCs() {
		int statesInAllBalls = 0;
		int max = 0;
		for (final StronglyConnectedComponent<NODE> scc : mBalls) {
			statesInAllBalls += scc.getNumberOfStates();
			max = Math.max(max, scc.getNumberOfStates());
		}
		mLogger.debug("The biggest SCC has " + max + " vertices.");
		final boolean sameNumberOfVertices = statesInAllBalls + mNumberOfNonBallSCCs == mNumberOfAllStates;
		return sameNumberOfVertices;
	}

	/**
	 * Stack and Set in one object. Elements that are already contained must not be added.
	 *
	 * @author Matthias Heizmann
	 *
	 */
	static class StackHashSet<NODE> {
		private final Deque<NODE> mStack = new ArrayDeque<>();
		private final Set<NODE> mSet = new HashSet<>();

		public NODE pop() {
			final NODE node = mStack.pop();
			mSet.remove(node);
			return node;
		}

		public void push(final NODE node) {
			mStack.push(node);
			final boolean modified = mSet.add(node);
			if (!modified) {
				throw new IllegalArgumentException("Illegal to add element twice " + node);
			}
		}

		public boolean contains(final NODE node) {
			return mSet.contains(node);
		}
	}

	@FunctionalInterface
	public interface IStronglyConnectedComponentFactory<NODE, C extends StronglyConnectedComponent<NODE>> {
		C constructNewSCComponent();
	}

	@FunctionalInterface
	public interface ISuccessorProvider<NODE> {
		Iterator<NODE> getSuccessors(NODE node);
	}
}
