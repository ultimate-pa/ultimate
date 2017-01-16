/*
 * Copyright (C) 2015-2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractCounterexample;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class AbstractInterpretationResult<STATE extends IAbstractState<STATE, VARDECL>, ACTION, VARDECL, LOCATION>
		implements IAbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> {

	private final IAbstractDomain<STATE, ACTION, VARDECL> mAbstractDomain;
	private final List<AbstractCounterexample<AbstractMultiState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION>> mCounterexamples;
	private final AbstractInterpretationBenchmark<ACTION, LOCATION> mBenchmark;
	private final Map<LOCATION, Term> mLoc2Term;
	private final Map<LOCATION, Set<STATE>> mLoc2States;
	private final Map<LOCATION, STATE> mLoc2SingleStates;
	private final Set<Term> mTerms;
	private IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> mRootStorage;
	private ISummaryStorage<STATE, ACTION, VARDECL, LOCATION> mSummaryMap;
	private final ITransitionProvider<ACTION, LOCATION> mTransProvider;
	private final Class<VARDECL> mVariablesType;

	protected AbstractInterpretationResult(final IAbstractDomain<STATE, ACTION, VARDECL> abstractDomain,
			final ITransitionProvider<ACTION, LOCATION> transProvider, final Class<VARDECL> variablesType) {
		assert abstractDomain != null;
		mAbstractDomain = abstractDomain;
		mCounterexamples = new ArrayList<>();
		mBenchmark = new AbstractInterpretationBenchmark<>();
		mLoc2Term = new HashMap<>();
		mLoc2States = new HashMap<>();
		mLoc2SingleStates = new HashMap<>();
		mTerms = new LinkedHashSet<>();
		mTransProvider = transProvider;
		mVariablesType = variablesType;
	}

	void reachedError(final ITransitionProvider<ACTION, LOCATION> transitionProvider,
			final IWorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final AbstractMultiState<STATE, ACTION, VARDECL> postState) {

		final List<Triple<AbstractMultiState<STATE, ACTION, VARDECL>, LOCATION, ACTION>> abstractExecution =
				new ArrayList<>();

		ACTION transition = currentItem.getAction();
		abstractExecution.add(new Triple<>(postState, transitionProvider.getTarget(transition), transition));

		AbstractMultiState<STATE, ACTION, VARDECL> post = currentItem.getState();
		IWorklistItem<STATE, ACTION, VARDECL, LOCATION> current = currentItem.getPredecessor();
		while (current != null) {
			transition = current.getAction();
			abstractExecution.add(new Triple<>(post, transitionProvider.getTarget(transition), transition));
			post = current.getState();
			current = current.getPredecessor();
		}

		Collections.reverse(abstractExecution);
		mCounterexamples
				.add(new AbstractCounterexample<>(post, transitionProvider.getSource(transition), abstractExecution));
	}

	void saveRootStorage(final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> rootStateStorage,
			final ACTION start, final Script script) {
		mRootStorage = rootStateStorage;
		mTerms.addAll(rootStateStorage.getTerms(start, script));
		mLoc2Term.putAll(rootStateStorage.getLoc2Term(start, script));

		final Map<LOCATION, Set<AbstractMultiState<STATE, ACTION, VARDECL>>> loc2states =
				rootStateStorage.getLoc2States(start);
		loc2states.entrySet().forEach(a -> mLoc2States.put(a.getKey(),
				a.getValue().stream().flatMap(b -> b.getStates().stream()).collect(Collectors.toSet())));
		mLoc2SingleStates.putAll(rootStateStorage.getLoc2SingleStates(start));
	}

	void saveSummaryStorage(final ISummaryStorage<STATE, ACTION, VARDECL, LOCATION> summaryStorage) {
		mSummaryMap = summaryStorage;
	}

	@Override
	public Set<STATE> getPostStates(final Deque<ACTION> callStack, final ACTION symbol, final Set<STATE> preStates) {

		final Set<STATE> states = mRootStorage.getAbstractPostStates(callStack, symbol);

		if (states.isEmpty() && mTransProvider.isEnteringScope(symbol)) {
			// because this is a call, it could also be somewhere in the summary map
			final AbstractMultiState<STATE, ACTION, VARDECL> summaryState =
					mSummaryMap.getSummaryPostState(symbol, new AbstractMultiState<>(preStates, mVariablesType));
			if (summaryState != null) {
				states.addAll(summaryState.getStates());
			}
		}

		return states;
	}

	@Override
	public Map<LOCATION, Term> getLoc2Term() {
		return mLoc2Term;
	}

	@Override
	public Map<LOCATION, Set<STATE>> getLoc2States() {
		return mLoc2States;
	}

	@Override
	public Map<LOCATION, STATE> getLoc2SingleStates() {
		return mLoc2SingleStates;
	}

	@Override
	public List<AbstractCounterexample<AbstractMultiState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION>>
			getCounterexamples() {
		return mCounterexamples;
	}

	@Override
	public boolean hasReachedError() {
		return !mCounterexamples.isEmpty();
	}

	public AbstractInterpretationBenchmark<ACTION, LOCATION> getBenchmark() {
		return mBenchmark;
	}

	@Override
	public Set<Term> getTerms() {
		return mTerms;
	}

	@Override
	public String toString() {
		return toSimplifiedString(a -> a.toStringDirect());
	}

	@Override
	public String toSimplifiedString(final Function<Term, String> funSimplify) {
		final StringBuilder sb = new StringBuilder();
		if (hasReachedError()) {
			sb.append("AI reached error location.");
		} else {
			sb.append("AI did not reach error location.");
		}
		if (getTerms() != null) {
			sb.append(" Found terms ");
			sb.append(String.join(", ", getTerms().stream().map(funSimplify::apply).collect(Collectors.toList())));
		}
		return sb.toString();
	}

	@Override
	public IAbstractDomain<STATE, ACTION, VARDECL> getUsedDomain() {
		return mAbstractDomain;
	}
}
