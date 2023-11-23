/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.BetterLockstepOrder.RoundRobinComparator;

/**
 * A DFS order that aims to place context switches between threads whenever (and only when) a loop head is reached.
 *
 * For n threads of form "init; (loop)*; finish", the minimal traces under full commutativity should be
 * "init1,...,init_n,(loop1,...,loop_n)*,finish1,...,finish_n" (if all threads loop the same number of times).
 *
 * This order is stateful, i.e., to apply it you need to wrap the searched automaton in a sort of product, see
 * {@link #wrapAutomaton(INwaOutgoingLetterAndTransitionProvider)}. Thus the reduced automaton can grow significantly.
 * The hope is however that reductions using this order admit simpler proofs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the reduced automaton. We need ICFG transitions to notice when we reach a loop head
 *            in a thread.
 */
public class LoopLockstepOrder<L extends IIcfgTransition<?>> implements IDfsOrder<L, IPredicate> {

	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);
	private final IIcfg<?> mIcfg;
	private final UnaryOperator<IPredicate> mNormalize;

	public LoopLockstepOrder(final IIcfg<?> icfg, final UnaryOperator<IPredicate> normalize) {
		mIcfg = icfg;
		mNormalize = normalize;
	}

	@Override
	public Comparator<L> getOrder(final IPredicate state) {
		final IPredicate original = mNormalize == null ? state : mNormalize.apply(state);
		if (original instanceof PredicateWithLastThread) {
			return new RoundRobinComparator<>(((PredicateWithLastThread) original).getLastThread(), mDefaultComparator);
		}
		throw new IllegalArgumentException("Expected PredicateWithLastThread, got " + original);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate>
			wrapAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(automaton) : "No calls and returns supported";
		final Optional<String> maxThread =
				IcfgUtils.getAllThreadInstances(mIcfg).stream().min(Comparator.naturalOrder());
		assert maxThread.isPresent() : "No thread found";
		return new WrapperAutomaton<>(automaton, maxThread.get(), mIcfg.getLoopLocations());
	}

	private static final class WrapperAutomaton<L extends IIcfgTransition<?>>
			implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate> {
		private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mUnderlying;
		private final String mMaxThread;
		private final Set<? extends IcfgLocation> mLoopHeads;

		private final Map<PredicateWithLastThread, PredicateWithLastThread> mKnownStates = new HashMap<>();

		private WrapperAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton,
				final String maxThread, final Set<? extends IcfgLocation> loopHeads) {
			mUnderlying = automaton;
			mMaxThread = maxThread;
			mLoopHeads = loopHeads;
		}

		@Override
		public IStateFactory<IPredicate> getStateFactory() {
			throw new UnsupportedOperationException();
		}

		@Override
		public VpAlphabet<L> getVpAlphabet() {
			return mUnderlying.getVpAlphabet();
		}

		@Override
		public IPredicate getEmptyStackState() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Iterable<IPredicate> getInitialStates() {
			return StreamSupport.stream(mUnderlying.getInitialStates().spliterator(), false)
					.map(q -> getOrCreateState(q, mMaxThread)).collect(Collectors.toSet());
		}

		@Override
		public boolean isInitial(final IPredicate state) {
			if (state instanceof PredicateWithLastThread) {
				return mUnderlying.isFinal(((PredicateWithLastThread) state).getUnderlying())
						&& mMaxThread.equals(((PredicateWithLastThread) state).getLastThread());
			}
			throw new IllegalArgumentException();
		}

		@Override
		public boolean isFinal(final IPredicate state) {
			if (state instanceof PredicateWithLastThread) {
				return mUnderlying.isFinal(((PredicateWithLastThread) state).getUnderlying());
			}
			throw new IllegalArgumentException();
		}

		@Override
		public int size() {
			return -1;
		}

		@Override
		public String sizeInformation() {
			return "<unknown>";
		}

		@Override
		public Set<L> lettersInternal(final IPredicate state) {
			if (state instanceof PredicateWithLastThread) {
				return mUnderlying.lettersInternal(((PredicateWithLastThread) state).getUnderlying());
			}
			throw new IllegalArgumentException();
		}

		@Override
		public Iterable<OutgoingInternalTransition<L, IPredicate>> internalSuccessors(final IPredicate state,
				final L letter) {
			if (!(state instanceof PredicateWithLastThread)) {
				throw new IllegalArgumentException();
			}
			final PredicateWithLastThread predState = (PredicateWithLastThread) state;

			// Keep the same order between threads, until we reach a loop head. Then we shift the order by one thread.
			// This allows other threads to interrupt and "catch up" before we enter the loop and after every iteration.
			final String lastThread;
			final IcfgLocation target = letter.getTarget();
			if (mLoopHeads.contains(target)) {
				lastThread = target.getProcedure();
			} else {
				lastThread = predState.getLastThread();
			}

			return StreamSupport
					.stream(mUnderlying.internalSuccessors(predState.getUnderlying(), letter).spliterator(), false)
					.map(outgoing -> new OutgoingInternalTransition<>(letter,
							getOrCreateState(outgoing.getSucc(), lastThread)))
					.collect(Collectors.toSet());
		}

		@Override
		public Iterable<OutgoingCallTransition<L, IPredicate>> callSuccessors(final IPredicate state, final L letter) {
			throw new UnsupportedOperationException();
		}

		@Override
		public Iterable<OutgoingReturnTransition<L, IPredicate>> returnSuccessors(final IPredicate state,
				final IPredicate hier, final L letter) {
			throw new UnsupportedOperationException();
		}

		private IPredicate getOrCreateState(final IPredicate underlying, final String lastThread) {
			final var newState = new PredicateWithLastThread((IMLPredicate) underlying, lastThread);
			return mKnownStates.computeIfAbsent(newState, Function.identity());
		}
	}

	public static final class PredicateWithLastThread extends AnnotatedMLPredicate<String> {
		private PredicateWithLastThread(final IMLPredicate underlying, final String lastThread) {
			super(underlying, lastThread);
		}

		public String getLastThread() {
			return mAnnotation;
		}

		@Override
		public String toString() {
			return "PredicateWithLastThread [last=" + mAnnotation + ", underlying=" + mUnderlying + "]";
		}
	}
}
