/*
 * Copyright (C) 2015 Jeffery Hsu (a71128@gmail.com)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 *
 * This is an implementation of incremental inclusion check based on the Bn baseline Algorithm.<br/>
 * We use InclusionViaDIfference to check its correctness.
 *
 * @author jefferyyjhsu@iis.sinica.edu.tw
 *
 * @param <LETTER>
 * @param <STATE>
 */

public class IncrementalInclusionCheck2DeadEndRemoval<LETTER, STATE>
		extends AbstractIncrementalInclusionCheck<LETTER, STATE> implements IOperation<LETTER, STATE> {
	private int mCounterRun = 0;
	private int mCounterTotalNodes = 0;
	private final INestedWordAutomatonSimple<LETTER, STATE> mLocalMA;
	private final List<INestedWordAutomatonSimple<LETTER, STATE>> mLocalMB;
	private final List<INestedWordAutomatonSimple<LETTER, STATE>> mLocalMB2;
	private final IDeterminizeStateFactory<STATE> mLocalStateFactory;
	private final AutomataLibraryServices mLocalServiceProvider;
	private HashSet<NodeData<LETTER, STATE>> mAllNodes;
	private LinkedList<NodeData<LETTER, STATE>> mErrorNodes;
	private LinkedList<NodeData<LETTER, STATE>> mCurrentTree;
	private LinkedList<NodeData<LETTER, STATE>> mAlreadyDeletedNodes;
	private LinkedList<NodeData<LETTER, STATE>> mCompleteTree;
	private LinkedList<NodeData<LETTER, STATE>> mCoveredNodes;
	private HashSet<NodeData<LETTER, STATE>> toBeKeepedNodes;

	public IncrementalInclusionCheck2DeadEndRemoval(final AutomataLibraryServices services,
			final IDeterminizeStateFactory<STATE> sf, final INestedWordAutomatonSimple<LETTER, STATE> a,
			final List<INestedWordAutomatonSimple<LETTER, STATE>> b) throws AutomataLibraryException {
		super(services, a);
		IncrementalInclusionCheck2DeadEndRemoval.abortIfContainsCallOrReturn(a);
		mLocalServiceProvider = services;
		mLocalStateFactory = sf;
		mLogger.info(startMessage());
		mLocalMA = (new RemoveDeadEnds<>(mLocalServiceProvider, a)).getResult();
		mLocalMB = new ArrayList<>();
		mLocalMB2 = new ArrayList<>();
		for (final INestedWordAutomatonSimple<LETTER, STATE> bn : b) {
			final INestedWordAutomatonSimple<LETTER, STATE> tempB =
					(new RemoveDeadEnds<>(mLocalServiceProvider, bn)).getResult();
			try {
				super.addSubtrahend(tempB);
			} catch (final AutomataLibraryException e) {
				mLogger.fatal(e);
			}
			mLocalMB.add(tempB);
			mLocalMB2.add(tempB);
		}
		run();
		mLogger.info(exitMessage());
	}

	@Override
	public void addSubtrahend(final INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		mLogger.info(startMessage());
		final INestedWordAutomatonSimple<LETTER, STATE> tempB =
				(new RemoveDeadEnds<>(mLocalServiceProvider, nwa)).getResult();
		super.addSubtrahend(tempB);
		mLocalMB.add(tempB);
		mLocalMB2.add(tempB);
		LinkedList<NodeData<LETTER, STATE>> bufferedTree = null;
		if (mErrorNodes.peekFirst() != null) {
			addBStates(tempB);
			do {
				mCounterRun++;
				if (cover()) {
					deadEndRemove();
					break;
				}
				if (!mServices.getProgressAwareTimer().continueProcessing()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
				bufferedTree = null;
				bufferedTree = expand(false);
				mCurrentTree = bufferedTree;
				exceptionRun();
			} while (true);
		}
		mLogger.info(exitMessage());
	}

	public void run() throws AutomataLibraryException {
		LinkedList<NodeData<LETTER, STATE>> bufferedTree = null;
		mCoveredNodes = new LinkedList<>();
		mAllNodes = new HashSet<>();
		mAlreadyDeletedNodes = new LinkedList<>();
		mErrorNodes = new LinkedList<>();
		mCompleteTree = null;
		mCurrentTree = null;
		for (final INestedWordAutomatonSimple<LETTER, STATE> B : mLocalMB) {
			if (!mLocalMA.getAlphabet().containsAll(B.getAlphabet())) {
				mLogger.info("Alphabet inconsistent");
				return;
			}
		}
		do {
			mCounterRun++;
			if (mCurrentTree == null) {
				mCurrentTree = expand(true);
				exceptionRun();
				if (cover()) {
					deadEndRemove();
					break;
				}
			} else {
				if (!mServices.getProgressAwareTimer().continueProcessing()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
				bufferedTree = expand(false);
				mCurrentTree = bufferedTree;
				exceptionRun();
				if (cover()) {
					deadEndRemove();
					break;
				}
			}
		} while (true);
	}

	@SuppressWarnings("unchecked")
	private LinkedList<NodeData<LETTER, STATE>> expand(final boolean init) {
		final LinkedList<NodeData<LETTER, STATE>> nextNodes = new LinkedList<>();
		HashMap<INestedWordAutomatonSimple<LETTER, STATE>, HashSet<STATE>> bStates = null;
		NodeData<LETTER, STATE> tempNodeData = null;
		int tempHash;
		if (init == true) {
			tempHash = 0;
			bStates = new HashMap<>();
			for (final INestedWordAutomatonSimple<LETTER, STATE> automata : mLocalMB) {
				bStates.put(automata, new HashSet<STATE>());
				for (final STATE Bstate : automata.getInitialStates()) {
					bStates.get(automata).add(Bstate);
					tempHash = tempHash | Bstate.hashCode();
				}
			}
			for (final STATE state : mLocalMA.getInitialStates()) {
				tempNodeData = new NodeData<>(new NestedRun<LETTER, STATE>(state));
				tempNodeData.mParentNode = null;
				tempNodeData.mHash = tempHash;
				tempNodeData.mBStates = (Map<INestedWordAutomatonSimple<LETTER, STATE>, Set<STATE>>) bStates.clone();
				mCounterTotalNodes++;
				tempNodeData.mAState = state;
				mAllNodes.add(tempNodeData);
				nextNodes.add(tempNodeData);
			}
		} else {
			for (final NodeData<LETTER, STATE> currentNodeSet : mCurrentTree) {
				for (final OutgoingInternalTransition<LETTER, STATE> ATransition : mLocalMA
						.internalSuccessors(currentNodeSet.mAState)) {
					boolean alreadyExisted = false;
					tempHash = 0;
					bStates = new HashMap<>();
					for (final INestedWordAutomatonSimple<LETTER, STATE> automata : currentNodeSet.mBStates.keySet()) {
						bStates.put(automata, new HashSet<STATE>());
						for (final STATE Bstate : currentNodeSet.mBStates.get(automata)) {
							for (final OutgoingInternalTransition<LETTER, STATE> BTransition : automata
									.internalSuccessors(Bstate, ATransition.getLetter())) {
								bStates.get(automata).add(BTransition.getSucc());
								tempHash = tempHash | BTransition.getSucc().hashCode();
							}
						}
					}
					final ArrayList<STATE> newStateSequence =
							(ArrayList<STATE>) currentNodeSet.mWord.getStateSequence().clone();
					newStateSequence.add(ATransition.getSucc());
					tempNodeData = new NodeData<>(new NestedRun<>(
							currentNodeSet.mWord.getWord().concatenate(new NestedWord<>(ATransition.getLetter(), -2)),
							newStateSequence));
					tempNodeData.mAState = ATransition.getSucc();
					tempNodeData.mParentNode = currentNodeSet;
					tempNodeData.mHash = tempHash;
					tempNodeData.mBStates = new HashMap<>();
					for (final INestedWordAutomatonSimple<LETTER, STATE> automata : bStates.keySet()) {
						tempNodeData.mBStates.put(automata, (HashSet<STATE>) bStates.get(automata).clone());
					}
					for (final NodeData<LETTER, STATE> deletedNode : mAlreadyDeletedNodes) {
						if (deletedNode.mAState.equals(tempNodeData.mAState)) {
							alreadyExisted = true;
							for (final INestedWordAutomatonSimple<LETTER, STATE> automata : deletedNode.mBStates
									.keySet()) {
								if (!deletedNode.mBStates.get(automata).equals(tempNodeData.mBStates.get(automata))) {
									alreadyExisted = false;
									break;
								}
							}
							if (alreadyExisted) {
								break;
							}
						}
					}
					if (!alreadyExisted) {
						mCounterTotalNodes++;
						mAllNodes.add(tempNodeData);
						nextNodes.add(tempNodeData);
					}
				}
			}
		}
		return nextNodes;
	}

	private boolean cover() {
		boolean newNodeInCompleteTree = false;
		boolean containsAllbnState = false;
		final LinkedList<NodeData<LETTER, STATE>> toBeDeleteed = new LinkedList<>();
		int i;
		int j;
		for (i = 0; i < mCurrentTree.size(); i++) {
			final NodeData<LETTER, STATE> currentNodeSet1 = mCurrentTree.get(i);
			containsAllbnState = false;
			if (mCompleteTree != null) {
				for (final NodeData<LETTER, STATE> completeNodeSet : mCompleteTree) {
					if ((currentNodeSet1.mAState.equals(completeNodeSet.mAState))
							&& completeNodeSet.mHash == (currentNodeSet1.mHash & completeNodeSet.mHash)
							&& (currentNodeSet1.mBStates.size() == completeNodeSet.mBStates.size())) {
						containsAllbnState = true;
						for (final INestedWordAutomatonSimple<LETTER, STATE> bn : currentNodeSet1.mBStates.keySet()) {
							if (!currentNodeSet1.mBStates.get(bn).equals(completeNodeSet.mBStates.get(bn))) {
								containsAllbnState = false;
							}
						}
						if (containsAllbnState) {
							completeNodeSet.mCovering.add(currentNodeSet1);
							break;
						}
					}
				}
			} else {
				containsAllbnState = false;
				mCompleteTree = new LinkedList<>();
			}
			if (containsAllbnState) {
				currentNodeSet1.mCovered = true;
				mCoveredNodes.add(currentNodeSet1);
				toBeDeleteed.add(currentNodeSet1);
			} else {
				containsAllbnState = false;
				for (j = 0; j < i; j++) {
					final NodeData<LETTER, STATE> currentNodeSet2 = mCurrentTree.get(j);
					if (currentNodeSet1 != currentNodeSet2 && !(currentNodeSet2.mCovered)
							&& (currentNodeSet1.mAState.equals(currentNodeSet2.mAState))
							&& (currentNodeSet2.mHash == (currentNodeSet1.mHash & currentNodeSet2.mHash)
									&& (currentNodeSet2.mBStates.size() == currentNodeSet1.mBStates.size()))) {
						containsAllbnState = true;
						for (final INestedWordAutomatonSimple<LETTER, STATE> bn : currentNodeSet2.mBStates.keySet()) {
							if (!currentNodeSet1.mBStates.get(bn).equals(currentNodeSet2.mBStates.get(bn))) {
								containsAllbnState = false;
							}
						}
						if (containsAllbnState) {
							currentNodeSet2.mCovering.add(currentNodeSet1);
							break;
						}
					}
				}
				if (!containsAllbnState) {
					newNodeInCompleteTree = true;
					mCompleteTree.add(currentNodeSet1);
				} else {
					currentNodeSet1.mCovered = true;
					mCoveredNodes.add(currentNodeSet1);
					toBeDeleteed.add(currentNodeSet1);
				}
			}
		}
		mCurrentTree.removeAll(toBeDeleteed);
		return !newNodeInCompleteTree;
	}

	private boolean exceptionRun() {
		boolean foundFinal = false;
		for (final NodeData<LETTER, STATE> currentNodeSet : mCurrentTree) {
			if (mLocalMA.isFinal(currentNodeSet.mAState)) {
				foundFinal = false;
				for (final INestedWordAutomatonSimple<LETTER, STATE> bn : currentNodeSet.mBStates.keySet()) {
					for (final STATE bnState : currentNodeSet.mBStates.get(bn)) {
						if (bn.isFinal(bnState)) {
							foundFinal = true;
							break;
						}
					}
					if (foundFinal) {
						break;
					}
				}
				if (!foundFinal) {
					mErrorNodes.add(currentNodeSet);
				}
			}
		}
		return mErrorNodes.peek() != null;
	}

	@Override
	public NestedRun<LETTER, STATE> getCounterexample() {
		if (mErrorNodes.peekFirst() != null) {
			return mErrorNodes.peekFirst().mWord;
		}
		return null;
	}

	@Override
	public String operationName() {
		return "IncrementalInclusionCheck2DeadEndRemovalDeadEndRemoval";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName();
	}

	@Override
	public String exitMessage() {
		if (mErrorNodes.peekFirst() != null) {
			mLogger.info("counterExample: " + mErrorNodes.peekFirst().mWord.getWord().toString());
		}
		mLogger.info("Total error: " + mErrorNodes.size() + " errors");
		mLogger.info("total:" + mCounterTotalNodes + "nodes");
		mLogger.info("total:" + mAllNodes.size() + "nodes");
		mLogger.info(mCompleteTree.size() + "nodes in the end");
		mLogger.info("total:" + mCounterRun + "runs");
		return "Exit " + operationName();
	}

	@Override
	public Boolean getResult() {
		return mErrorNodes.peekFirst() == null;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		boolean checkResult;
		// TODO Christian 2017-02-16 Casts are temporary workarounds until state factory becomes class parameter
		if (mErrorNodes.peekFirst() != null) {
			checkResult = compareInclusionCheckResult(mLocalServiceProvider,
					(IDeterminizeStateFactory<STATE> & IIntersectionStateFactory<STATE>) stateFactory, mLocalMA,
					mLocalMB2, mErrorNodes.peekFirst().mWord);
		} else {
			checkResult = compareInclusionCheckResult(mLocalServiceProvider,
					(IDeterminizeStateFactory<STATE> & IIntersectionStateFactory<STATE>) stateFactory, mLocalMA,
					mLocalMB2, null);
		}
		return checkResult;
	}

	/**
	 * Compare the result of an inclusion check with an inclusion check based on a emptiness/difference operations. The
	 * NestedRun ctrEx is the result of an inclusion check whose inputs are an automaton <b>a</b> and and a list of
	 * automata b. If the language of <b>a</b> is included in the union of all languages of the automata b then ctrEx is
	 * null, otherwise ctrEx is a run of <b>a</b> that is a counterexample to the inclusion. This method returns true if
	 * the difference-based inclusion check comes up with the same result, i.e., if it find a counterexample if ctrEx is
	 * non-null and if it does not find a counterexample if ctrEX is null. Note that if inclusion does not hold, there
	 * may be several counterexamples. Dies method does NOT require that both methods return exactly the same
	 * counterexample.
	 */
	public static <LETTER, STATE, FACTORY extends IDeterminizeStateFactory<STATE> & IIntersectionStateFactory<STATE>>
		boolean compareInclusionCheckResult(final AutomataLibraryServices services,
			final FACTORY stateFactory, final INestedWordAutomatonSimple<LETTER, STATE> a,
			final List<INestedWordAutomatonSimple<LETTER, STATE>> b, final NestedRun<LETTER, STATE> ctrEx)
			throws AutomataLibraryException {
		final InclusionViaDifference<LETTER, STATE> ivd = new InclusionViaDifference<>(services, stateFactory, a);
		// add all b automata
		for (final INestedWordAutomatonSimple<LETTER, STATE> bi : b) {
			ivd.addSubtrahend(bi);
		}
		// obtain counterexample, counterexample is null if inclusion holds
		final NestedRun<LETTER, STATE> ivdCounterexample = ivd.getCounterexample();
		// return true iff both counterexamples are null or both counterexamples
		// are non-null.
		boolean result;
		if (ivdCounterexample == null) {
			if (ctrEx == null) {
				result = true;
			} else {
				result = false;
			}
		} else {
			if (ctrEx == null) {
				result = false;
			} else {
				result = true;
			}
		}
		return result;
	}

	private HashSet<STATE> nestedRunStates(final INestedWordAutomatonSimple<LETTER, STATE> bn,
			final NestedRun<LETTER, STATE> word) {
		HashSet<STATE> curStaSet = null;
		Iterable<OutgoingInternalTransition<LETTER, STATE>> nextStaSet = null;
		HashSet<STATE> newStaSet;
		curStaSet = new HashSet<>();
		for (final STATE state : bn.getInitialStates()) {
			curStaSet.add(state);
		}
		if (word.getWord().length() != 0) {
			for (final LETTER alphabet : word.getWord().asList()) {
				newStaSet = new HashSet<>();
				for (final STATE OState : curStaSet) {
					nextStaSet = bn.internalSuccessors(OState, alphabet);
					for (final OutgoingInternalTransition<LETTER, STATE> newState : nextStaSet) {
						newStaSet.add(newState.getSucc());
					}
				}
				curStaSet.clear();
				curStaSet = newStaSet;
			}
		}
		return curStaSet;
	}

	private void deadEndRemove() {
		mLogger.info("Node size before delete: " + mCompleteTree.size());
		mCompleteTree.size();
		toBeKeepedNodes = new HashSet<>();
		int i = 0;
		HashSet<NodeData<LETTER, STATE>> toBeDeletedNodes = new HashSet<>(mAllNodes);
		for (final NodeData<LETTER, STATE> node : mAllNodes) {
			node.mKeep = false;
		}
		for (final NodeData<LETTER, STATE> errorNode : mErrorNodes) {
			deadEndRemoveWalker(errorNode);
		}
		toBeDeletedNodes.removeAll(toBeKeepedNodes);
		for (final NodeData<LETTER, STATE> nodeToBeDelete : toBeDeletedNodes) {
			for (final NodeData<LETTER, STATE> uncoverNode : nodeToBeDelete.mCovering) {
				uncoverNode.mCovered = false;
			}
			nodeToBeDelete.mCovering.clear();
			if (mCompleteTree.contains(nodeToBeDelete)) {
				mCompleteTree.remove(nodeToBeDelete);
				mAlreadyDeletedNodes.add(nodeToBeDelete);
				i++;
			} else {
				if (mCoveredNodes.contains(nodeToBeDelete)) {
					mCoveredNodes.remove(nodeToBeDelete);
				}
			}
		}
		mAllNodes.removeAll(toBeDeletedNodes);
		mLogger.info("DeadEndRemove removes " + i + "nodes.");
		mLogger.info("Node size after delete: " + mCompleteTree.size());
		toBeDeletedNodes = null;
		toBeKeepedNodes = null;
	}

	private void deadEndRemoveWalker(final NodeData<LETTER, STATE> node) {
		assert node != null;
		if (!node.mKeep) {
			node.mKeep = true;
			toBeKeepedNodes.add(node);
			for (final NodeData<LETTER, STATE> coveringNode : node.mCovering) {
				deadEndRemoveWalker(coveringNode);
			}
			if (node.mParentNode != null) {
				deadEndRemoveWalker(node.mParentNode);
			}
		}
	}

	private void addBStates(final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		HashSet<STATE> newStates = null;
		if (mCompleteTree != null) {
			for (final NodeData<LETTER, STATE> node : mCompleteTree) {
				node.mBStates.put(nwa, new HashSet<STATE>());
				newStates = nestedRunStates(nwa, node.mWord);
				node.mBStates.get(nwa).addAll(newStates);
				for (final STATE s : newStates) {
					node.mHash = node.mHash | s.hashCode();
				}
				if (node.mCovering != null) {
					node.mCovering.clear();
				}
			}
		}
		mCurrentTree.addAll(mCoveredNodes);
		mCoveredNodes.clear();
		for (final NodeData<LETTER, STATE> node : mCurrentTree) {
			node.mCovered = false;
			node.mBStates.put(nwa, new HashSet<STATE>());
			newStates = nestedRunStates(nwa, node.mWord);
			node.mBStates.get(nwa).addAll(newStates);
			for (final STATE s : newStates) {
				node.mHash = node.mHash | s.hashCode();
			}
		}
		checkErrorNodesAfterAddingB();
	}

	private void checkErrorNodesAfterAddingB() {
		boolean foundFinal = false;
		final HashSet<NodeData<LETTER, STATE>> toBeDeletedNodes = new HashSet<>();
		for (final NodeData<LETTER, STATE> checkingNode : mErrorNodes) {
			foundFinal = false;
			for (final INestedWordAutomatonSimple<LETTER, STATE> bn : checkingNode.mBStates.keySet()) {
				for (final STATE bnState : checkingNode.mBStates.get(bn)) {
					if (bn.isFinal(bnState)) {
						foundFinal = true;
						break;
					}
				}
				if (foundFinal) {
					toBeDeletedNodes.add(checkingNode);
					break;
				}
			}
		}
		mErrorNodes.removeAll(toBeDeletedNodes);
		return;

	}

	public static <LETTER, STATE> void abortIfContainsCallOrReturn(final INestedWordAutomatonSimple<LETTER, STATE> a) {
		if (!a.getCallAlphabet().isEmpty() || !a.getReturnAlphabet().isEmpty()) {
			throw new UnsupportedOperationException("Operation does not support call or return");
		}
	}

	private static final class NodeData<A, B> {
		public boolean mKeep;
		public int mHash;
		public boolean mCovered = false;
		public NodeData<A, B> mParentNode;
		public Set<NodeData<A, B>> mCovering;
		public B mAState;
		public Map<INestedWordAutomatonSimple<A, B>, Set<B>> mBStates;
		public NestedRun<A, B> mWord;

		public NodeData(final NestedRun<A, B> data) {
			mBStates = new HashMap<>();
			mWord = data;
			mCovering = new HashSet<>();
		}
	}
}
