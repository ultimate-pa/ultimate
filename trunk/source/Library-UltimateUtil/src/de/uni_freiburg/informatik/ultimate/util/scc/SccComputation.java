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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Computes strongly connected components (SCCs) of a graph. 
 * Implementation of Tarjan SCC algorithm. 
 * {@link http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm}
 * @param <NODE> Type of objects that represent nodes of the graph.
 * @param <COMP> Type of objects that represent strongly connected components.
 * 
 * @author heizmann@informatik.uni-freiburg.de
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
	int mIndex = 0;
	/**
	 * Vertices that have not yet been assigned to any SCC.
	 */
	protected final StackHashSet<NODE> mNoScc = new StackHashSet<NODE>();
	/**
	 * Assigns to each vertex v the number of vertices that have been
	 * processed before in this algorithm. This number is called the index
	 * of v.
	 */
	protected final Map<NODE, Integer> mIndices = new HashMap<NODE, Integer>();
	protected final Map<NODE, Integer> mLowLinks = new HashMap<NODE, Integer>();
	protected final ArrayList<COMP> mBalls = new ArrayList<COMP>();
	protected final ArrayList<COMP> mSCCs = new ArrayList<COMP>();
	private int mNumberOfNonBallSCCs = 0;

	


	public SccComputation(ILogger logger,
			ISuccessorProvider<NODE> successorProvider,
			IStronglyConnectedComponentFactory<NODE, COMP> sccFac,
			int numberOfAllNodes,
			Set<NODE> startNodes) {
		super();
		mLogger = logger;
		mSccFactory = sccFac;
		mSuccessorProvider = successorProvider;
		mNumberOfAllStates = numberOfAllNodes;
		
		for (NODE node : startNodes) {
			if (!mIndices.containsKey(node)) {
				strongconnect(node);
			}
		}
		assert (automatonPartitionedBySCCs());
		mLogger.info("Graph consists of " + getBalls().size() + 
				" InCaSumBalls and " + mNumberOfNonBallSCCs
				+ " non ball SCCs. Number of states in SCCs "
				+ mNumberOfAllStates + ".");
	}


	public interface IStronglyConnectedComponentFactory<NODE, C extends StronglyConnectedComponent<NODE>> {
			public C constructNewSCComponent();
	}
	
	public interface ISuccessorProvider<NODE> {
		public Iterator<NODE> getSuccessors(NODE node);
	}

	public Collection<COMP> getBalls() {
		return Collections.unmodifiableList(mBalls);
	}
	
	/**
	 * @return a list of all SCCs (ball SCCs and non-ball SCCs). If SCC a is
	 * reachable from SCC b, then SCC a occurs in this list before SCC b
	 * (reverse topological order with respect to reachability).
	 */
	public List<COMP> getSCCs() {
		return Collections.unmodifiableList(mSCCs);
	}

	protected void strongconnect(NODE v) {
		assert (!mIndices.containsKey(v));
		assert (!mLowLinks.containsKey(v));
		mIndices.put(v, mIndex);
		mLowLinks.put(v, mIndex);
		mIndex++;
		this.mNoScc.push(v);
		
		Iterator<NODE> it = mSuccessorProvider.getSuccessors(v);
		while(it.hasNext()) {
			NODE succCont = it.next();
			processSuccessor(v, succCont);
		}
	
		if (mLowLinks.get(v).equals(mIndices.get(v))) {
			establishNewComponent(v);
		}
	}

	protected void establishNewComponent(NODE v) {
		NODE w;
		COMP scc = mSccFactory.constructNewSCComponent();
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

	private void processSuccessor(NODE v, NODE w) {
		if (!mIndices.containsKey(w)) {
			strongconnect(w);
			updateLowlink(v, mLowLinks.get(w));
		} else if (mNoScc.contains(w)) {
			updateLowlink(v, mIndices.get(w));
		}
	}

	protected void updateLowlink(NODE node, int newValueCandidate) {
		int min = Math.min(mLowLinks.get(node), newValueCandidate);
		mLowLinks.put(node, min);
	}

	boolean isBall(StronglyConnectedComponent<NODE> scc) {
		if (scc.getNumberOfStates() == 1) {
			NODE cont = scc.getRootNode();
			Iterator<NODE> it = mSuccessorProvider.getSuccessors(cont);
			while(it.hasNext()) {
				NODE succCont = it.next();
				if (cont.equals(succCont)) {
					return true;
				}
			}
			return false;
		} else {
			assert scc.getNumberOfStates() > 1;
			return true;
		}
	}

	/**
	 * @return true iff the SCCS form a partition of the automaton.
	 */
	protected boolean automatonPartitionedBySCCs() {
		int statesInAllBalls = 0;
		int max = 0;
		for (StronglyConnectedComponent<NODE> scc : mBalls) {
			statesInAllBalls += scc.getNumberOfStates();
			max = Math.max(max, scc.getNumberOfStates());
		}
		mLogger.debug("The biggest SCC has " + max + " vertices.");
		boolean sameNumberOfVertices = (statesInAllBalls + mNumberOfNonBallSCCs == mNumberOfAllStates);
		return sameNumberOfVertices;
	}


	/**
	 * Stack and Set in one object. Elements that are already contained 
	 * must not be added.
	 * @author Matthias Heizmann
	 *
	 */
	class StackHashSet<NODE> {
		private final Stack<NODE> mStack = new Stack<>();
		private final Set<NODE> mSet = new HashSet<>();
		
		public NODE pop() {
			NODE node = mStack.pop();
			mSet.remove(node);
			return node;
		}
		
		public void push(NODE node) {
			mStack.push(node);
			boolean modified = mSet.add(node);
			if (!modified) {
				throw new IllegalArgumentException("Illegal to add element twice " + node);
			}
		}
		
		public boolean contains(NODE node) {
			return mSet.contains(node);
		}
	}


}
