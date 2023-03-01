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
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states
 */
public class UnfoldToTree<L, S> implements INwaOutgoingLetterAndTransitionProvider<L, UnfoldToTree.TreeNode<L, S>> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final TreeNode<L, S> mRoot;

	private final NwaCacheBookkeeping<L, TreeNode<L, S>> mCacheBookkeeping = new NwaCacheBookkeeping<>();
	private final NestedWordAutomatonCache<L, TreeNode<L, S>> mCache;

	public UnfoldToTree(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand) {
		this(services, operand, DataStructureUtils.getOneAndOnly(operand.getInitialStates(), "initial state"));
	}

	public UnfoldToTree(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final S initial) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Operand must be finite automaton";
		mOperand = operand;

		mCache = new NestedWordAutomatonCache<>(services, mOperand.getVpAlphabet(), () -> null);

		mRoot = new TreeNode<>(initial);
		mCache.addState(true, mOperand.isFinal(initial), mRoot);
	}

	@Deprecated
	@Override
	public IStateFactory<TreeNode<L, S>> getStateFactory() {
		throw new UnsupportedOperationException();
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public TreeNode<L, S> getEmptyStackState() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<TreeNode<L, S>> getInitialStates() {
		return Set.of(mRoot);
	}

	@Override
	public boolean isInitial(final TreeNode<L, S> state) {
		return state == mRoot;
	}

	@Override
	public boolean isFinal(final TreeNode<L, S> state) {
		return mOperand.isFinal(state.getCurrentState());
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
	public Set<L> lettersInternal(final TreeNode<L, S> state) {
		return mOperand.lettersInternal(state.getCurrentState());
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, TreeNode<L, S>>> internalSuccessors(final TreeNode<L, S> state,
			final L letter) {
		if (!mCacheBookkeeping.isCachedInternal(state, letter)) {
			final var transitions = mOperand.internalSuccessors(state.getCurrentState(), letter);
			final var transition = DataStructureUtils.getOnly(transitions, "Automaton must be deterministic");
			if (!transition.isEmpty() && !state.containsState(transition.get().getSucc())) {
				final var child = new TreeNode<>(state, transition.get());

				final var successor = transition.get().getSucc();
				mCache.addState(false, mOperand.isFinal(successor), child);

				mCache.addInternalTransition(state, letter, child);
			}
			mCacheBookkeeping.reportCachedInternal(state, letter);
		}
		return mCache.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<L, TreeNode<L, S>>> callSuccessors(final TreeNode<L, S> state,
			final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, TreeNode<L, S>>> returnSuccessors(final TreeNode<L, S> state,
			final TreeNode<L, S> hier, final L letter) {
		return Collections.emptySet();
	}

	public static final class TreeNode<L, S> {
		private final S mRoot;
		private final ImmutableList<OutgoingInternalTransition<L, S>> mPath;

		private TreeNode(final S root) {
			mRoot = root;
			mPath = ImmutableList.empty();
		}

		private TreeNode(final TreeNode<L, S> parent, final OutgoingInternalTransition<L, S> transition) {
			mRoot = parent.mRoot;
			mPath = new ImmutableList<>(transition, parent.mPath);
		}

		public S getCurrentState() {
			if (mPath.isEmpty()) {
				return mRoot;
			}
			return mPath.getHead().getSucc();
		}

		public S getRoot() {
			return mRoot;
		}

		public ImmutableList<OutgoingInternalTransition<L, S>> getPath() {
			return mPath;
		}

		private boolean containsState(final S state) {
			return mRoot.equals(state) || mPath.stream().anyMatch(t -> t.getSucc().equals(state));
		}
	}
}
