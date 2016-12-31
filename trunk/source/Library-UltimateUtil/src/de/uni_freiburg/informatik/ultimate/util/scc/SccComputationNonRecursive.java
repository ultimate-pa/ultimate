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
import java.util.Deque;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Non-recursive implementation of {@link SccComputation}.
 * 
 * @author Matthias Heizmann
 *
 * @param <NODE>
 */
public class SccComputationNonRecursive<NODE, COMP extends StronglyConnectedComponent<NODE>>
		extends SccComputation<NODE, COMP> {

	public SccComputationNonRecursive(final ILogger logger, final ISuccessorProvider<NODE> successorProvider,
			final IStronglyConnectedComponentFactory<NODE, COMP> sccFac, final int numberOfAllNodes,
			final Set<NODE> startNodes) {
		super(logger, successorProvider, sccFac, numberOfAllNodes, startNodes);
	}

	@Override
	protected void strongconnect(final NODE v) {
		final Deque<TodoStackElement> todoStack = new ArrayDeque<>();
		todoStack.push(new TodoStackElement(v, null));
		while (!todoStack.isEmpty()) {
			final TodoStackElement todoStackElement = todoStack.pop();
			switch (todoStackElement.getTask()) {
			case INDEX:
				if (mIndices.containsKey(todoStackElement.getNode())) {
					// do nothing
				} else {
					doIndex(todoStackElement.getNode());
					todoStackElement.reportTaskAccomplished();
					todoStack.push(todoStackElement);
				}
				break;
			case GET_SUCCESSORS:
				todoStackElement.reportTaskAccomplished();
				todoStack.push(todoStackElement);
				doGetSuccessors(todoStackElement.getNode(), todoStack);
				break;
			case SET_LOWLINK:
				doSetLowlink(todoStackElement.getNode(), todoStackElement.getPredecessor());
				break;
			default:
				throw new AssertionError();
			}
		}
	}

	private void doSetLowlink(final NODE node, final NODE predecessor) {
		if (mLowLinks.get(node).equals(mIndices.get(node))) {
			establishNewComponent(node);
		}
		if (predecessor == null) {
			// node is first element, do nothing
		} else {
			updateLowlink(predecessor, mLowLinks.get(node));
		}
	}

	private void doGetSuccessors(final NODE node, final Deque<TodoStackElement> todoStack) {
		final Iterator<NODE> it = mSuccessorProvider.getSuccessors(node);
		while (it.hasNext()) {
			final NODE succ = it.next();
			if (mIndices.containsKey(succ)) {
				if (mNoScc.contains(succ)) {
					updateLowlink(node, mIndices.get(succ));
				}
			} else {
				todoStack.push(new TodoStackElement(succ, node));
			}
		}
	}

	private void doIndex(final NODE node) {
		assert !mIndices.containsKey(node);
		assert !mLowLinks.containsKey(node);
		mIndices.put(node, mIndex);
		mLowLinks.put(node, mIndex);
		mIndex++;
		mNoScc.push(node);
	}

	enum NextTask {
		INDEX, GET_SUCCESSORS, SET_LOWLINK
	}

	private class TodoStackElement {
		private final NODE mNode;
		private NextTask mTask;
		private final NODE mPredecessor;

		public TodoStackElement(final NODE node, final NODE predecessor) {
			super();
			mNode = node;
			mTask = NextTask.INDEX;
			mPredecessor = predecessor;
		}

		public void reportTaskAccomplished() {
			switch (mTask) {
			case INDEX:
				mTask = NextTask.GET_SUCCESSORS;
				break;
			case GET_SUCCESSORS:
				mTask = NextTask.SET_LOWLINK;
				break;
			case SET_LOWLINK:
				throw new IllegalStateException("SET_LOWLINK is last task");
			default:
				throw new AssertionError();
			}
		}

		public NODE getNode() {
			return mNode;
		}

		public NextTask getTask() {
			return mTask;
		}

		public NODE getPredecessor() {
			return mPredecessor;
		}

		@Override
		public String toString() {
			return "TodoStackElement [mNode=" + mNode + ", mTask=" + mTask + ", mPredecessor=" + mPredecessor + "]";
		}
	}
}
