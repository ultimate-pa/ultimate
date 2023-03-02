/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaCacheBookkeeping;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

/**
 * Unfolds a finite automaton into a tree. In other words, when multiple words would lead to the same state, we instead
 * have two separate states. Loops back to a previously visited state are removed from the automaton.
 *
 * Any word accepted by the unfolded automaton is also accepted by the input automaton. The language of the unfolded
 * automaton is empty if and only if the language of the input automaton is empty.
 *
 * Call and return edges are not supported.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states
 */
public class UnfoldToTree<L, S, U> implements INwaOutgoingLetterAndTransitionProvider<L, U> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final U mRoot;
	private final IUnfoldStateFactory<L, S, U> mStateFactory;

	private final NwaCacheBookkeeping<L, U> mCacheBookkeeping = new NwaCacheBookkeeping<>();
	private final NestedWordAutomatonCache<L, U> mCache;

	public UnfoldToTree(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IUnfoldStateFactory<L, S, U> stateFactory) {
		this(services, operand, DataStructureUtils.getOneAndOnly(operand.getInitialStates(), "initial state"),
				stateFactory);
	}

	public UnfoldToTree(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final S initial,
			final IUnfoldStateFactory<L, S, U> stateFactory) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Operand must be finite automaton";
		mOperand = operand;
		mStateFactory = stateFactory;

		mCache = new NestedWordAutomatonCache<>(services, mOperand.getVpAlphabet(), () -> null);

		mRoot = mStateFactory.treeNode(initial, ImmutableList.empty());
		mCache.addState(true, mOperand.isFinal(initial), mRoot);
	}

	@Deprecated
	@Override
	public IStateFactory<U> getStateFactory() {
		throw new UnsupportedOperationException();
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public U getEmptyStackState() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<U> getInitialStates() {
		return Set.of(mRoot);
	}

	@Override
	public boolean isInitial(final U treeNode) {
		return treeNode == mRoot;
	}

	@Override
	public boolean isFinal(final U treeNode) {
		return mOperand.isFinal(mStateFactory.getCurrentState(treeNode));
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "<unknown size>";
	}

	@Override
	public Set<L> lettersInternal(final U treeNode) {
		return mOperand.lettersInternal(mStateFactory.getCurrentState(treeNode));
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, U>> internalSuccessors(final U treeNode, final L letter) {
		if (!mCacheBookkeeping.isCachedInternal(treeNode, letter)) {
			final var transitions = mOperand.internalSuccessors(mStateFactory.getCurrentState(treeNode), letter);
			final var transition = DataStructureUtils.getOnly(transitions, "Automaton must be deterministic");
			if (!transition.isEmpty() && !containsState(treeNode, transition.get().getSucc())) {
				final var childPath = new ImmutableList<>(transition.get(), mStateFactory.getPath(treeNode));
				final var child = mStateFactory.treeNode(mStateFactory.getRoot(treeNode), childPath);

				final var successor = transition.get().getSucc();
				mCache.addState(false, mOperand.isFinal(successor), child);

				mCache.addInternalTransition(treeNode, letter, child);
			}
			mCacheBookkeeping.reportCachedInternal(treeNode, letter);
		}
		return mCache.internalSuccessors(treeNode, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<L, U>> callSuccessors(final U treeNode, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, U>> returnSuccessors(final U treeNode, final U hier, final L letter) {
		return Collections.emptySet();
	}

	private boolean containsState(final U treeNode, final S state) {
		return mStateFactory.getRoot(treeNode).equals(state)
				|| mStateFactory.getPath(treeNode).stream().anyMatch(t -> t.getSucc().equals(state));
	}

	/**
	 * A state factory used to unfold finite automata into trees.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters
	 * @param <S>
	 *            The type of states in the input automaton
	 * @param <U>
	 *            The type of states in the unfolded automaton
	 */
	public interface IUnfoldStateFactory<L, S, U> extends IStateFactory<U> {
		/**
		 * Creates a new state (or "tree node") of the unfolded automaton.
		 *
		 * @param root
		 *            The state representing the root of the unfodled tree (typically, an initial state)
		 * @param path
		 *            The path of transitions from the root to the current node. The path is reversed, i.e., the first
		 *            transition in the list is the last transition in the path.
		 * @return the new tree node
		 */
		U treeNode(S root, ImmutableList<OutgoingInternalTransition<L, S>> path);

		/**
		 * Retrieves the root from a tree node created by this factory
		 *
		 * @param treeNode
		 *            A state of the unfolded automaton, created by {@link #treeNode(S, ImmutableList)}
		 * @return The state of the input automaton that was passed to the {@link #treeNode(S, ImmutableList)} call that
		 *         created the given tree node
		 */
		S getRoot(U treeNode);

		/**
		 * Retrieves the path from a tree node created by this factory
		 *
		 * @param treeNode
		 *            A state of the unfolded automaton, created by {@link #treeNode(S, ImmutableList)}
		 * @return The path of transitions that was passed to the {@link #treeNode(S, ImmutableList)} call that created
		 *         the given tree node
		 */
		ImmutableList<OutgoingInternalTransition<L, S>> getPath(U treeNode);

		/**
		 * Retrieves the current state of the input automaton corresponding to a given state of the unfolded automaton.
		 *
		 * @param treeNode
		 *            the state of the unfolded automaton
		 * @return the last state in the path represented by the given tree node (the root, if the path is empty)
		 */
		default S getCurrentState(final U treeNode) {
			final var path = getPath(treeNode);
			if (path.isEmpty()) {
				return getRoot(treeNode);
			}
			return path.getHead().getSucc();
		}
	}
}
