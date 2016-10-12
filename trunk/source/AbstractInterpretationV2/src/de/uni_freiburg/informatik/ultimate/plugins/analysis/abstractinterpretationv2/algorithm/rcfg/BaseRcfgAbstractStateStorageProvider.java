/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public abstract class BaseRcfgAbstractStateStorageProvider<STATE extends IAbstractState<STATE, CodeBlock, VARDECL>, LOCATION, VARDECL>
		implements IAbstractStateStorage<STATE, CodeBlock, VARDECL, LOCATION> {

	private final IAbstractStateBinaryOperator<STATE> mMergeOperator;
	private final IUltimateServiceProvider mServices;
	private final Set<BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL>> mChildStores;
	private final ITransitionProvider<CodeBlock, LOCATION> mTransProvider;
	private final CodeBlock mScope;
	private final Set<CodeBlock> mScopeFixpoints;
	private final BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> mParent;

	public BaseRcfgAbstractStateStorageProvider(final IAbstractStateBinaryOperator<STATE> mergeOperator,
			final IUltimateServiceProvider services, final ITransitionProvider<CodeBlock, LOCATION> transProvider,
			final CodeBlock scope, final BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> parent) {
		assert mergeOperator != null;
		assert services != null;
		assert transProvider != null;
		mMergeOperator = mergeOperator;
		mServices = services;
		mTransProvider = transProvider;
		mChildStores = new HashSet<>();
		mScope = scope;
		mScopeFixpoints = new HashSet<>();
		mParent = parent;
	}

	@Override
	public AbstractMultiState<STATE, CodeBlock, VARDECL> addAbstractPostState(final CodeBlock transition,
			final AbstractMultiState<STATE, CodeBlock, VARDECL> state) {
		assert transition != null : "Cannot add state to null transition";
		assert state != null : "Cannot add null state";
		final AbstractMultiState<STATE, CodeBlock, VARDECL> oldState = getPostState(transition);
		if (oldState == null) {
			replacePostState(transition, state);
			return state;
		}
		final AbstractMultiState<STATE, CodeBlock, VARDECL> mergedState = oldState.merge(mMergeOperator, state);
		replacePostState(transition, mergedState);
		return mergedState;
	}

	@Override
	public final IAbstractStateStorage<STATE, CodeBlock, VARDECL, LOCATION> createStorage(final CodeBlock scope) {
		final BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> rtr = create(scope, this);
		mChildStores.add(rtr);
		return rtr;
	}

	@Override
	public Map<LOCATION, Term> getLoc2Term(final CodeBlock initialTransition, final Script script,
			final Boogie2SMT bpl2smt) {
		// TODO: What shall we do about different scopes? Currently, states at the same location are merged and later
		// converted to terms. This leads to loss of precision, so that tools relying on those terms cannot prove
		// absence of errors with the terms alone, even if AI was able to prove it.
		final Map<LOCATION, StateDecorator> states = getMergedStatesOfAllChildren(initialTransition);
		return convertStates2Terms(states, script, bpl2smt);
	}

	@Override
	public final Map<LOCATION, Set<AbstractMultiState<STATE, CodeBlock, VARDECL>>>
			getLoc2States(final CodeBlock initialTransition) {
		final Map<LOCATION, Set<AbstractMultiState<STATE, CodeBlock, VARDECL>>> states =
				getStatesOfAllChildren(initialTransition);
		return states.entrySet().stream().filter(e -> e.getValue() != null && !e.getValue().isEmpty())
				.collect(Collectors.toMap(e -> e.getKey(), v -> v.getValue()));
	}

	@Override
	public Map<LOCATION, STATE> getLoc2SingleStates(final CodeBlock initialTransition) {
		final Map<LOCATION, StateDecorator> states = getMergedStatesOfAllChildren(initialTransition);
		return states.entrySet().stream().filter(e -> e.getValue().mState != null).collect(Collectors
				.toMap(Map.Entry::getKey, decorator -> decorator.getValue().mState.getSingleState(mMergeOperator)));
	}

	@Override
	public Set<Term> getTerms(final CodeBlock initialTransition, final Script script, final Boogie2SMT bpl2smt) {
		final Set<Term> rtr = new LinkedHashSet<>();
		getLocalTerms(initialTransition, script, bpl2smt, rtr);
		mChildStores.stream().filter(a -> a != this)
				.forEach(a -> rtr.addAll(a.getTerms(initialTransition, script, bpl2smt)));
		return rtr;
	}

	@Override
	public AbstractMultiState<STATE, CodeBlock, VARDECL> getAbstractPostStates(final CodeBlock transition) {
		assert transition != null;
		return getPostState(transition);
	}

	@Override
	public Set<STATE> getAbstractPostStates(final Deque<CodeBlock> callStack, final CodeBlock symbol) {
		assert symbol != null;
		assert mScope == null;
		if (callStack.isEmpty()) {
			return Optional.ofNullable(getAbstractPostStates(symbol)).map(a -> a.getStates())
					.orElse(Collections.emptySet());
		}

		final Iterator<CodeBlock> iterator = callStack.descendingIterator();
		List<BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL>> currentChilds =
				Collections.singletonList(this);
		while (iterator.hasNext()) {
			final CodeBlock currentScope = iterator.next();

			final List<BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL>> newChilds =
					currentChilds.stream().flatMap(a -> a.mChildStores.stream()).filter(a -> a.mScope == currentScope)
							.collect(Collectors.toList());
			currentChilds.stream().filter(a -> a.containsScopeFixpoint(currentScope)).forEach(newChilds::add);
			currentChilds = newChilds;
		}

		final Set<STATE> rtr = currentChilds.stream().map(a -> Optional.ofNullable(a.getAbstractPostStates(symbol))
				.map(b -> b.getStates()).orElse(Collections.emptySet())).flatMap(a -> a.stream())
				.collect(Collectors.toSet());

		// if (rtr.isEmpty() && symbol instanceof Return) {
		// return getAbstractPostStates(callStack, symbol);
		// }

		return rtr;
	}

	@Override
	public void scopeFixpointReached() {
		mParent.mScopeFixpoints.add(mScope);
	}

	private Map<LOCATION, StateDecorator> getMergedStatesOfAllChildren(final CodeBlock initialTransition) {
		Map<LOCATION, StateDecorator> states = getMergedLocalStates(initialTransition);
		for (final BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> child : mChildStores.stream()
				.filter(a -> a != this).collect(Collectors.toSet())) {
			states = mergeMaps(states, child.getMergedStatesOfAllChildren(initialTransition), (a, b) -> a.merge(b));
		}
		return states;
	}

	private Map<LOCATION, Set<AbstractMultiState<STATE, CodeBlock, VARDECL>>>
			getStatesOfAllChildren(final CodeBlock initialTransition) {
		Map<LOCATION, Set<AbstractMultiState<STATE, CodeBlock, VARDECL>>> states = getLocalStates(initialTransition);
		for (final BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> child : mChildStores.stream()
				.filter(a -> a != this).collect(Collectors.toSet())) {
			states = mergeMaps(states, child.getStatesOfAllChildren(initialTransition));
		}
		return states;
	}

	private Map<LOCATION, StateDecorator> getMergedLocalStates(final CodeBlock initialTransition) {
		final Map<LOCATION, StateDecorator> rtr = new HashMap<>();
		final Deque<CodeBlock> worklist = new ArrayDeque<>();
		final Set<CodeBlock> closed = new HashSet<>();

		worklist.add(initialTransition);

		while (!worklist.isEmpty()) {
			final CodeBlock current = worklist.remove();
			// check if already processed
			if (!closed.add(current)) {
				continue;
			}

			final LOCATION postLoc = mTransProvider.getTarget(current);
			// add successors to worklist
			for (final CodeBlock outgoing : mTransProvider.getSuccessorActions(postLoc)) {
				worklist.add(outgoing);
			}

			final AbstractMultiState<STATE, CodeBlock, VARDECL> states = getPostState(current);

			final StateDecorator currentState;
			if (states == null || states.isEmpty()) {
				// no states for this location
				currentState = new StateDecorator();
			} else {
				currentState = new StateDecorator(states);
			}

			final StateDecorator alreadyKnownState = rtr.get(postLoc);
			if (alreadyKnownState != null) {
				rtr.put(postLoc, alreadyKnownState.merge(currentState));
			} else {
				rtr.put(postLoc, currentState);
			}

		}
		return rtr;
	}

	private Map<LOCATION, Set<AbstractMultiState<STATE, CodeBlock, VARDECL>>>
			getLocalStates(final CodeBlock initialTransition) {
		final Map<LOCATION, Set<AbstractMultiState<STATE, CodeBlock, VARDECL>>> rtr = new HashMap<>();
		final Deque<CodeBlock> worklist = new ArrayDeque<>();
		final Set<CodeBlock> closed = new HashSet<>();

		worklist.add(initialTransition);

		while (!worklist.isEmpty()) {
			final CodeBlock current = worklist.remove();

			if (!closed.add(current)) {
				continue;
			}

			final LOCATION postLoc = mTransProvider.getTarget(current);

			for (final CodeBlock outgoing : mTransProvider.getSuccessorActions(postLoc)) {
				worklist.add(outgoing);
			}

			Set<AbstractMultiState<STATE, CodeBlock, VARDECL>> alreadyKnownStates = rtr.get(postLoc);
			if (alreadyKnownStates == null) {
				alreadyKnownStates = new HashSet<>();
				rtr.put(postLoc, alreadyKnownStates);
			}

			final AbstractMultiState<STATE, CodeBlock, VARDECL> postState = getPostState(current);
			if (postState == null) {
				continue;
			}
			alreadyKnownStates.add(postState);
		}
		return rtr;
	}

	private Set<Term> getLocalTerms(final CodeBlock initialTransition, final Script script, final Boogie2SMT bpl2smt,
			final Set<Term> terms) {
		final Deque<CodeBlock> worklist = new ArrayDeque<>();
		final Set<CodeBlock> closed = new LinkedHashSet<>();

		worklist.add(initialTransition);

		final Term falseTerm = script.term("false");

		while (!worklist.isEmpty()) {
			final CodeBlock current = worklist.remove();
			// check if already processed
			if (!closed.add(current)) {
				continue;
			}

			final LOCATION postLoc = mTransProvider.getTarget(current);
			// add successors to worklist
			for (final CodeBlock outgoing : mTransProvider.getSuccessorActions(postLoc)) {
				worklist.add(outgoing);
			}

			final AbstractMultiState<STATE, CodeBlock, VARDECL> multiState = getPostState(current);

			if (multiState == null || multiState.isEmpty()) {
				// no states for this location
				terms.add(falseTerm);
			} else {
				terms.add(multiState.getTerm(script, bpl2smt));
			}
		}
		return terms;
	}

	private static <K, V> Map<K, V> mergeMaps(final Map<K, V> a, final Map<K, V> b, final BiFunction<V, V, V> merge) {
		final Map<K, V> rtr = new HashMap<>();

		for (final Entry<K, V> entryA : a.entrySet()) {
			final V valueB = b.get(entryA.getKey());
			if (valueB == null) {
				rtr.put(entryA.getKey(), entryA.getValue());
			} else {
				rtr.put(entryA.getKey(), merge.apply(entryA.getValue(), valueB));
			}
		}

		for (final Entry<K, V> entryB : b.entrySet()) {
			final V valueA = a.get(entryB.getKey());
			if (valueA == null) {
				rtr.put(entryB.getKey(), entryB.getValue());
			} else {
				// do nothing, this was already done in first iteration
			}
		}
		return rtr;
	}

	private static <K, V> Map<K, Set<V>> mergeMaps(final Map<K, Set<V>> one, final Map<K, Set<V>> other) {
		return mergeMaps(one, other, (a, b) -> {
			assert a != null && b != null;
			final Set<V> newSet = new HashSet<>();
			newSet.addAll(a);
			newSet.addAll(b);
			return newSet;
		});
	}

	private Map<LOCATION, Term> convertStates2Terms(final Map<LOCATION, StateDecorator> states, final Script script,
			final Boogie2SMT bpl2smt) {
		final Map<LOCATION, Term> rtr = new HashMap<>();

		for (final Entry<LOCATION, StateDecorator> entry : states.entrySet()) {
			final Term term = entry.getValue().getTerm(script, bpl2smt);
			final LOCATION loc = entry.getKey();
			rtr.put(loc, term);
		}

		return rtr;
	}

	private boolean containsScopeFixpoint(final CodeBlock scope) {
		return mScopeFixpoints.contains(scope);
	}

	protected abstract BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> create(CodeBlock scope,
			BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> parent);

	protected abstract AbstractMultiState<STATE, CodeBlock, VARDECL> getPostState(CodeBlock action);

	protected abstract void replacePostState(final CodeBlock action,
			final AbstractMultiState<STATE, CodeBlock, VARDECL> newState);

	protected abstract boolean isEmpty();

	protected IAbstractStateBinaryOperator<STATE> getMergeOperator() {
		return mMergeOperator;
	}

	protected IUltimateServiceProvider getServices() {
		return mServices;
	}

	protected ITransitionProvider<CodeBlock, LOCATION> getTransitionProvider() {
		return mTransProvider;
	}

	private final class StateDecorator {
		private final AbstractMultiState<STATE, CodeBlock, VARDECL> mState;

		private StateDecorator() {
			mState = null;
		}

		private StateDecorator(final AbstractMultiState<STATE, CodeBlock, VARDECL> state) {
			mState = state;
		}

		private Term getTerm(final Script script, final Boogie2SMT bpl2smt) {
			if (mState == null) {
				return script.term("false");
			}
			return mState.getTerm(script, bpl2smt);
		}

		private StateDecorator merge(final StateDecorator other) {
			if (other == null || other.mState == null) {
				return this;
			}
			if (mState == null) {
				return other;
			}
			return new StateDecorator(mState.merge(mMergeOperator, other.mState));
		}

		@Override
		public String toString() {
			return mState == null ? "null" : "\"" + mState.toLogString() + "\"";
		}
	}
}
