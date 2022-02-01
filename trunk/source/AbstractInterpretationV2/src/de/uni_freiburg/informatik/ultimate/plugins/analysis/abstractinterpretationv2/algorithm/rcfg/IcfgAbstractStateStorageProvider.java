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
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class IcfgAbstractStateStorageProvider<STATE extends IAbstractState<STATE>, ACTION extends IAction, LOC, VARDECL>
		implements IAbstractStateStorage<STATE, ACTION, LOC> {

	private final Map<LOC, DisjunctiveAbstractState<STATE>> mStorage;
	private final IUltimateServiceProvider mServices;
	private final Set<IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL>> mChildStores;
	private final ITransitionProvider<ACTION, LOC> mTransProvider;
	private final ACTION mScope;
	private final Set<ACTION> mScopeFixpoints;
	private final IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL> mParent;
	private final Set<String> mUsedSummary;

	public IcfgAbstractStateStorageProvider(final IUltimateServiceProvider services,
			final ITransitionProvider<ACTION, LOC> transprovider) {
		this(services, transprovider, null, null, new HashSet<>());
	}

	private IcfgAbstractStateStorageProvider(final IUltimateServiceProvider services,
			final ITransitionProvider<ACTION, LOC> transProvider, final ACTION scope,
			final IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL> parent, final Set<String> usedSummary) {
		assert services != null;
		assert transProvider != null;
		mServices = services;
		mTransProvider = transProvider;
		mScope = scope;
		mParent = parent;
		mChildStores = new HashSet<>();
		mScopeFixpoints = new HashSet<>();
		mStorage = new HashMap<>();
		mUsedSummary = usedSummary;
	}

	@Override
	public DisjunctiveAbstractState<STATE> addAbstractState(final LOC loc,
			final DisjunctiveAbstractState<STATE> state) {
		assert loc != null : "Cannot add state to non-existing location";
		assert state != null : "Cannot add null state";
		final DisjunctiveAbstractState<STATE> oldState = mStorage.get(loc);
		if (oldState == null) {
			mStorage.put(loc, state);
			return state;
		}
		final DisjunctiveAbstractState<STATE> mergedState = oldState.saturatedUnion(state);
		mStorage.put(loc, mergedState);
		return mergedState;
	}

	@Override
	public final IAbstractStateStorage<STATE, ACTION, LOC> createStorage(final ACTION scope) {
		final IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL> rtr =
				new IcfgAbstractStateStorageProvider<>(getServices(), getTransitionProvider(), scope, this,
						mUsedSummary);
		mChildStores.add(rtr);
		return rtr;
	}

	@Override
	public final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> computeLoc2States() {
		final Set<IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL>> stores = getAllStores();
		final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2states = new HashMap<>();
		for (final IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL> store : stores) {
			for (final Entry<LOC, DisjunctiveAbstractState<STATE>> entry : store.mStorage.entrySet()) {
				final Set<DisjunctiveAbstractState<STATE>> set = loc2states.get(entry.getKey());
				if (set == null) {
					final Set<DisjunctiveAbstractState<STATE>> newSet = new HashSet<>();
					newSet.add(entry.getValue());
					loc2states.put(entry.getKey(), newSet);
				} else {
					set.add(entry.getValue());
				}
			}
		}
		return loc2states;
	}

	@Override
	public DisjunctiveAbstractState<STATE> getAbstractState(final LOC loc) {
		return mStorage.get(loc);
	}

	@Override
	public Set<STATE> computeContextSensitiveAbstractPostStates(final Deque<ACTION> callStack, final ACTION symbol) {
		assert symbol != null;
		assert mScope == null;
		final Set<Pair<Deque<ACTION>, ACTION>> summaryCallStack = getSummaryCallStack(callStack, symbol);
		return getAbstractPostStatesWithSummary(summaryCallStack);
	}

	private Set<STATE> getAbstractPostStatesWithSummary(final Set<Pair<Deque<ACTION>, ACTION>> summaryCallStack) {
		final Set<STATE> rtr = new HashSet<>();
		summaryCallStack.forEach(a -> rtr.addAll(getAbstractPostStatesWithSummary(a.getFirst(), a.getSecond())));
		return rtr;
	}

	private Set<STATE> getAbstractPostStatesWithSummary(final Deque<ACTION> callStack, final ACTION symbol) {
		final Iterator<ACTION> iterator = callStack.descendingIterator();
		List<IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL>> currentChilds =
				Collections.singletonList(this);
		while (iterator.hasNext()) {
			final ACTION currentScope = iterator.next();

			final List<IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL>> newChilds =
					currentChilds.stream().flatMap(a -> a.mChildStores.stream()).filter(a -> a.mScope == currentScope)
							.collect(Collectors.toList());
			currentChilds.stream().filter(a -> a.containsScopeFixpoint(currentScope)).forEach(newChilds::add);
			currentChilds = newChilds;
		}
		final LOC target = mTransProvider.getTarget(symbol);
		final Set<STATE> rtr =
				currentChilds.stream().map(a -> Optional.ofNullable(a.getAbstractState(target)).map(b -> b.getStates())
						.orElse(Collections.emptySet())).flatMap(a -> a.stream()).collect(Collectors.toSet());
		return rtr;
	}

	private Set<Pair<Deque<ACTION>, ACTION>> getSummaryCallStack(final Deque<ACTION> callStack, final ACTION symbol) {
		// TODO: Unsure for what this was
		final Map<ACTION, Set<ACTION>> summarySourcesReturn = Collections.emptyMap();
		final Map<ACTION, Set<ACTION>> summarySourcesCall = Collections.emptyMap();

		final Set<ACTION> callsToReplace = callStack.stream()
				.filter(a -> mUsedSummary.contains(a.getSucceedingProcedure())).collect(Collectors.toSet());
		if (symbol instanceof IIcfgCallTransition<?> && mUsedSummary.contains(symbol.getSucceedingProcedure())) {
			callsToReplace.add(symbol);
		}
		final Set<ACTION> returnsToReplace = new HashSet<>();
		if (symbol instanceof IIcfgReturnTransition<?, ?> && mUsedSummary.contains(symbol.getPrecedingProcedure())) {
			returnsToReplace.addAll(summarySourcesReturn.get(symbol));
		}

		if (callsToReplace.isEmpty() && returnsToReplace.isEmpty()) {
			return Collections.singleton(new Pair<>(callStack, symbol));
		}

		final Comparator<ACTION> comparator = (o1, o2) -> Integer.compare(o1.hashCode(), o2.hashCode());

		final Pair<Map<ACTION, List<ACTION>>, Integer> callReplacementRulesPair =
				getReplacementRules(callsToReplace, comparator, summarySourcesCall);
		final Map<ACTION, List<ACTION>> callReplacementRules = callReplacementRulesPair.getFirst();
		final Map<ACTION, List<ACTION>> symbolReplacementRules;
		final int size;
		if (symbol instanceof IIcfgCallTransition<?>) {
			symbolReplacementRules = callReplacementRules;
			size = callReplacementRulesPair.getSecond();
		} else if (symbol instanceof IIcfgReturnTransition<?, ?>) {

			final Pair<Map<ACTION, List<ACTION>>, Integer> returnReplacementRulesPair =
					getReplacementRules(returnsToReplace, comparator, summarySourcesReturn);
			symbolReplacementRules = returnReplacementRulesPair.getFirst();
			size = Math.max(callReplacementRulesPair.getSecond(), returnReplacementRulesPair.getSecond());
		} else {
			symbolReplacementRules = Collections.emptyMap();
			size = callReplacementRulesPair.getSecond();
		}

		final Set<Pair<Deque<ACTION>, ACTION>> rtr = new HashSet<>();
		for (int i = 0; i < size; ++i) {
			final Deque<ACTION> newCallStack = new ArrayDeque<>();
			final Iterator<ACTION> iter = callStack.descendingIterator();
			while (iter.hasNext()) {
				final ACTION current = iter.next();
				newCallStack.addFirst(getMatchingSymbol(i, current, callReplacementRules.get(current)));
			}
			final ACTION newSymbol = getMatchingSymbol(i, symbol, symbolReplacementRules.get(symbol));
			rtr.add(new Pair<>(newCallStack, newSymbol));
		}

		return rtr;
	}

	private Pair<Map<ACTION, List<ACTION>>, Integer> getReplacementRules(final Set<ACTION> callsToReplace,
			final Comparator<ACTION> comparator, final Map<ACTION, Set<ACTION>> summarySourceProvider) {
		int size = 0;
		final Map<ACTION, List<ACTION>> callReplacementRules = new HashMap<>();
		for (final ACTION replace : callsToReplace) {
			final Set<ACTION> summarySources = summarySourceProvider.get(replace);
			assert !summarySources.isEmpty() : "Should use summary, but dont know which";
			callReplacementRules.put(replace, summarySources.stream().sorted(comparator).collect(Collectors.toList()));
			final int ssize = summarySources.size();
			size = Math.max(ssize, size);
		}
		return new Pair<>(callReplacementRules, size);
	}

	private ACTION getMatchingSymbol(final int i, final ACTION old, final List<ACTION> replacements) {
		if (replacements == null || replacements.isEmpty()) {
			return old;
		}
		final int size = replacements.size();
		if (i < size) {
			return replacements.get(i);
		}
		return replacements.get(size - 1);
	}

	@Override
	public void scopeFixpointReached() {
		mParent.mScopeFixpoints.add(mScope);
	}

	@Override
	public void saveSummarySubstituion(final ACTION action, final DisjunctiveAbstractState<STATE> summaryPostState,
			final ACTION summaryAction) {
		assert action instanceof IIcfgCallTransition<?>;
		mParent.mUsedSummary.add(action.getSucceedingProcedure());
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(mScope).append(" ");
		if (mStorage == null) {
			return sb.append("NULL").toString();
		}
		if (mStorage.isEmpty()) {
			return sb.append("{}").toString();
		}
		sb.append('{');
		final Set<Entry<LOC, DisjunctiveAbstractState<STATE>>> entries = mStorage.entrySet();
		for (final Entry<LOC, DisjunctiveAbstractState<STATE>> entry : entries) {
			sb.append(entry.getKey().toString()).append("=[");
			final DisjunctiveAbstractState<STATE> state = entry.getValue();
			if (!state.isEmpty()) {
				sb.append(state.toLogString());
			}
			sb.append("], ");
		}
		if (!entries.isEmpty()) {
			sb.delete(sb.length() - 2, sb.length());
		}
		sb.append('}');
		return sb.toString();
	}

	public String toTreeString() {
		return toTreeString(new StringBuilder(), "").toString();
	}

	public StringBuilder toTreeString(final StringBuilder sb, final String indent) {
		final String addIndent = "  ";
		sb.append(indent).append(toString()).append(CoreUtil.getPlatformLineSeparator());
		mChildStores.forEach(a -> a.toTreeString(sb, indent + addIndent));
		return sb;
	}

	private Set<IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL>> getAllStores() {
		final Set<IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL>> rtr = new HashSet<>();
		rtr.add(this);
		for (final IcfgAbstractStateStorageProvider<STATE, ACTION, LOC, VARDECL> child : mChildStores) {
			rtr.addAll(child.getAllStores());
		}
		return rtr;
	}

	private boolean containsScopeFixpoint(final ACTION scope) {
		return mScopeFixpoints.contains(scope);
	}

	protected IUltimateServiceProvider getServices() {
		return mServices;
	}

	protected ITransitionProvider<ACTION, LOC> getTransitionProvider() {
		return mTransProvider;
	}
}
