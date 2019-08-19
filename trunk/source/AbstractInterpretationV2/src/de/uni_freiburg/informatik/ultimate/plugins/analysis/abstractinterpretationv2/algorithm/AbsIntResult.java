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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.AbstractCounterexample;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class AbsIntResult<STATE extends IAbstractState<STATE>, ACTION, LOCATION>
		implements IAbstractInterpretationResult<STATE, ACTION, LOCATION> {

	private final IAbstractDomain<STATE, ACTION> mAbstractDomain;
	private final IVariableProvider<STATE, ACTION> mVariableProvider;
	private final ITransitionProvider<ACTION, LOCATION> mTransProvider;
	private final List<AbstractCounterexample<DisjunctiveAbstractState<STATE>, ACTION, LOCATION>> mCounterexamples;
	private final AbsIntBenchmark<ACTION> mBenchmark;

	private final Script mScript;

	private IAbstractStateStorage<STATE, ACTION, LOCATION> mRootStorage;
	private ISummaryStorage<STATE, ACTION, LOCATION> mSummaryMap;

	private Map<LOCATION, Term> mLoc2Term;
	private Map<LOCATION, Set<STATE>> mLoc2States;
	private Map<LOCATION, STATE> mLoc2SingleStates;
	private Set<Term> mTerms;

	protected AbsIntResult(final Script script, final IAbstractDomain<STATE, ACTION> abstractDomain,
			final ITransitionProvider<ACTION, LOCATION> transProvider,
			final IVariableProvider<STATE, ACTION> varProvider) {
		mAbstractDomain = Objects.requireNonNull(abstractDomain);
		mScript = Objects.requireNonNull(script);
		mTransProvider = Objects.requireNonNull(transProvider);
		mVariableProvider = Objects.requireNonNull(varProvider);
		mCounterexamples = new ArrayList<>();
		mBenchmark = new AbsIntBenchmark<>();

	}

	void reachedError(final ITransitionProvider<ACTION, LOCATION> transitionProvider,
			final IWorklistItem<STATE, ACTION, LOCATION> currentItem, final DisjunctiveAbstractState<STATE> postState) {

		final List<Triple<DisjunctiveAbstractState<STATE>, LOCATION, ACTION>> abstractExecution = new ArrayList<>();

		ACTION transition = currentItem.getAction();
		abstractExecution.add(getCexTriple(transitionProvider, postState, transition));

		DisjunctiveAbstractState<STATE> post = currentItem.getState();
		IWorklistItem<STATE, ACTION, LOCATION> current = currentItem.getPredecessor();
		while (current != null) {
			transition = current.getAction();
			abstractExecution.add(getCexTriple(transitionProvider, post, transition));
			post = current.getState();
			current = current.getPredecessor();
		}

		Collections.reverse(abstractExecution);
		mCounterexamples
				.add(new AbstractCounterexample<>(post, transitionProvider.getSource(transition), abstractExecution));
	}

	private Triple<DisjunctiveAbstractState<STATE>, LOCATION, ACTION> getCexTriple(
			final ITransitionProvider<ACTION, LOCATION> transitionProvider,
			final DisjunctiveAbstractState<STATE> postState, final ACTION transition) {
		return new Triple<>(postState, transitionProvider.getTarget(transition), transition);
	}

	void saveRootStorage(final IAbstractStateStorage<STATE, ACTION, LOCATION> rootStateStorage) {
		mRootStorage = rootStateStorage;
	}

	void saveSummaryStorage(final ISummaryStorage<STATE, ACTION, LOCATION> summaryStorage) {
		mSummaryMap = summaryStorage;
	}

	@Override
	public Set<STATE> getPostStates(final Deque<ACTION> callStack, final ACTION symbol, final Set<STATE> preStates) {
		final Set<STATE> states = mRootStorage.computeContextSensitiveAbstractPostStates(callStack, symbol);
		// TODO: this has to be disabled until summary calculation works correctly
		// because this is a call, it could also be somewhere in the summary map
		// if (states.isEmpty() && mTransProvider.isEnteringScope(symbol)) {
		// final AbstractMultiState<STATE> summaryState =
		// mSummaryMap.getSummaryPostState(symbol, new AbstractMultiState<>(preStates));
		// if (summaryState != null) {
		// states.addAll(summaryState.getStates());
		// }
		// }
		return states;
	}

	@Override
	public Map<LOCATION, Term> getLoc2Term() {
		if (mLoc2Term == null) {
			mLoc2Term = new HashMap<>();
			for (final Entry<LOCATION, STATE> entry : getLoc2SingleStates().entrySet()) {
				mLoc2Term.put(entry.getKey(), entry.getValue().getTerm(mScript));
			}
		}
		return mLoc2Term;
	}

	@Override
	public Map<LOCATION, Set<STATE>> getLoc2States() {
		if (mLoc2States == null) {
			mLoc2States = new HashMap<>();
			final Map<LOCATION, Set<DisjunctiveAbstractState<STATE>>> loc2multistates =
					mRootStorage.computeLoc2States();
			for (final Entry<LOCATION, Set<DisjunctiveAbstractState<STATE>>> entry : loc2multistates.entrySet()) {
				final Set<STATE> states =
						entry.getValue().stream().flatMap(a -> a.getStates().stream()).collect(Collectors.toSet());
				mLoc2States.put(entry.getKey(), states);
			}
		}
		return mLoc2States;
	}

	@Override
	public Map<LOCATION, STATE> getLoc2SingleStates() {
		if (mLoc2SingleStates == null) {
			mLoc2SingleStates = new HashMap<>();
			for (final Entry<LOCATION, Set<STATE>> entry : getLoc2States().entrySet()) {
				final Optional<STATE> singleState = entry.getValue().stream().reduce((a, b) -> a.union(b));
				if (singleState.isPresent()) {
					mLoc2SingleStates.put(entry.getKey(), singleState.get());
				}
			}
		}
		return mLoc2SingleStates;
	}

	@Override
	public Set<Term> getTerms() {
		if (mTerms == null) {
			mTerms = new HashSet<>();
			getLoc2Term().entrySet().stream().map(a -> a.getValue()).forEach(mTerms::add);
		}
		return mTerms;
	}

	@Override
	public IAbstractDomain<STATE, ACTION> getUsedDomain() {
		return mAbstractDomain;
	}

	@Override
	public IVariableProvider<STATE, ACTION> getUsedVariableProvider() {
		return mVariableProvider;
	}

	@Override
	public List<AbstractCounterexample<DisjunctiveAbstractState<STATE>, ACTION, LOCATION>> getCounterexamples() {
		return mCounterexamples;
	}

	@Override
	public boolean hasReachedError() {
		return !mCounterexamples.isEmpty();
	}

	@Override
	public AbsIntBenchmark<ACTION> getBenchmark() {
		return mBenchmark;
	}

	@Override
	public String toString() {
		return toSimplifiedString(Term::toStringDirect);
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

}
