package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

record SingleStateRecord<STATE extends IAbstractState<STATE>, LOC extends IcfgLocation>(STATE state,
		ThreadInstanceCounter threadCounter, AbstractLocationState<LOC> abstractLocationState) {

	public SingleStateRecord<STATE, LOC> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames) {
		return new SingleStateRecord<>(this.state(), this.threadCounter(),
				new AbstractLocationState<>(location, globalMap, threadNames));
	}

	public SingleStateRecord<STATE, LOC> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames, final Set<LOC> forkLocs) {
		var newState = new SingleStateRecord<>(this.state(), this.threadCounter(),
				new AbstractLocationState<>(location, globalMap, threadNames));
		for (final LOC loc : forkLocs) {
			newState = newState.movedTo(loc.getProcedure(), newState.abstractLocationState.getLocationMap()
					.getAbstractLocation((LOC) loc.getOutgoingNodes().iterator().next()));
		}
		return newState;
	}

	public SingleStateRecord<STATE, LOC> movedTo(final String threadName, final int newLocation) {
		return new SingleStateRecord<>(this.state(), this.threadCounter(),
				this.abstractLocationState().movedTo(threadName, newLocation));
	}

	public SingleStateRecord<STATE, LOC> setThreadsActive(final Collection<String> forkingStrings) {
		final var newThreadcounter = new ThreadInstanceCounter(threadCounter.setActive(forkingStrings));
		return new SingleStateRecord<>(this.state(), newThreadcounter, this.abstractLocationState());
	}

	public SingleStateRecord<STATE, LOC> setThreadsInf(final Collection<String> forkingStrings) {
		final var newThreadcounter = new ThreadInstanceCounter(threadCounter.setInf(forkingStrings));
		return new SingleStateRecord<>(this.state(), newThreadcounter, this.abstractLocationState());
	}

	public SingleStateRecord<STATE, LOC> incrementThread(final String thread) {
		final var newThreadcounter = this.threadCounter().incrementThread(thread);
		return new SingleStateRecord<>(this.state(), newThreadcounter, this.abstractLocationState());
	}

	public boolean isEqual(final SingleStateRecord<STATE, LOC> other) {
		if (!(other.state().isSubsetOf(this.state()) != SubsetResult.NONE)) {
			return false;
		}
		if (!other.threadCounter().isEqual(threadCounter)) {
			return false;
		}
		if (!other.abstractLocationState().isEqual(this.abstractLocationState())) {
			return false;
		}
		return true;
	}
}

public final class GuardedInterferenceDomainStateDisj<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractState<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> {

	private final IAbstractDomain<STATE, ACTION> mUnderlying;
	private final Set<SingleStateRecord<STATE, LOC>> mStates;
	private int MAXSIZE = 9999;

	public GuardedInterferenceDomainStateDisj(final IAbstractDomain<STATE, ACTION> underlying, final int maxSize,
			final Set<SingleStateRecord<STATE, LOC>> states) {
		mUnderlying = underlying;
		MAXSIZE = maxSize;
		mStates = new HashSet<>(reduceByEquality(states));
	}

	private Set<SingleStateRecord<STATE, LOC>> reduceByEquality(final Set<SingleStateRecord<STATE, LOC>> states) {
		final Set<SingleStateRecord<STATE, LOC>> reduced = new HashSet<>();
		for (final SingleStateRecord<STATE, LOC> record : states) {
			boolean duplicateFound = false;
			for (final SingleStateRecord<STATE, LOC> existingRecord : reduced) {
				if (existingRecord.isEqual(record)) {
					duplicateFound = true;
					break;
				}
			}
			if (!duplicateFound) {
				reduced.add(record);
			}
		}
		return reduced;
	}

	public GuardedInterferenceDomainStateDisj(final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		mStates = new HashSet<>(other.getStates());
		mUnderlying = other.getUnderlyingDomain();
	}

	// TODO:
	public GuardedInterferenceDomainStateDisj(final IAbstractDomain<STATE, ACTION> underlying, final int maxSize,
			final STATE state, final ThreadInstanceCounter threadcounter) {

		this(underlying, maxSize,
				Set.of(new SingleStateRecord<>(state, new ThreadInstanceCounter(threadcounter), null)));
	}

	public GuardedInterferenceDomainStateDisj(final IAbstractDomain<STATE, ACTION> underlying, final int maxSize,
			final STATE state, final ThreadInstanceCounter threadcounter, final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames) {

		this(underlying, maxSize, Set.of(new SingleStateRecord<>(state, new ThreadInstanceCounter(threadcounter),
				new AbstractLocationState<>(location, globalMap, threadNames))));
	}

	public GuardedInterferenceDomainStateDisj(final IAbstractDomain<STATE, ACTION> underlying, final int maxSize,
			final STATE state, final ThreadInstanceCounter threadcounter,
			final AbstractLocationState<LOC> abstractLocationState) {

		this(underlying, maxSize, Set
				.of(new SingleStateRecord<>(state, new ThreadInstanceCounter(threadcounter), abstractLocationState)));
	}

	public ThreadInstanceCounter getThreadInstanceState() {
		final var singleState = getSingleState();
		return singleState.threadCounter();
	}

	public Set<SingleStateRecord<STATE, LOC>> getStates() {
		return mStates;
	}

	public IAbstractDomain<STATE, ACTION> getUnderlyingDomain() {
		return mUnderlying;
	}

	/**
	 * Join of states, including threadcounter and abstractlocation
	 */
	public SingleStateRecord<STATE, LOC> getSingleState() {
		if (mStates.isEmpty()) {
			return null;
		}
		final var it = mStates.iterator();
		SingleStateRecord<STATE, LOC> merged = it.next();

		while (it.hasNext()) {
			final SingleStateRecord<STATE, LOC> next = it.next();
			final STATE mergedState = merged.state().union(next.state());
			final ThreadInstanceCounter mergedThreads = merged.threadCounter().union(next.threadCounter());
			final AbstractLocationState<LOC> mergedLocation = merged.abstractLocationState()
					.union(next.abstractLocationState());
			merged = new SingleStateRecord<>(mergedState, mergedThreads, mergedLocation);
		}
		return merged;
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames) {
		final var newStates = mStates.stream().map(s -> s.initializeLocation(location, globalMap, threadNames))
				.collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames, final Set<LOC> forkLocs) {
		final var newStates = mStates.stream()
				.map(s -> s.initializeLocation(location, globalMap, threadNames, forkLocs)).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> movedTo(final String threadName,
			final int newLocation) {
		final var newStates = mStates.stream().map(s -> s.movedTo(threadName, newLocation)).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> setThreadsActive(
			final Collection<String> forkingStrings) {
		final var newStates = mStates.stream().map(s -> s.setThreadsActive(forkingStrings)).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> setThreadsInf(
			final Collection<String> forkingStrings) {
		final var newStates = mStates.stream().map(s -> s.setThreadsInf(forkingStrings)).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> incrementThread(final String thread) {
		final var newStates = mStates.stream().map(s -> s.incrementThread(thread)).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> addVariable(final IProgramVarOrConst variable) {
		final var newStates = mStates.stream().map(s -> new SingleStateRecord<>(s.state().addVariable(variable),
				s.threadCounter(), s.abstractLocationState())).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> removeVariable(final IProgramVarOrConst variable) {
		final var newStates = mStates.stream().map(s -> new SingleStateRecord<>(s.state().removeVariable(variable),
				s.threadCounter(), s.abstractLocationState())).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> addVariables(
			final Collection<IProgramVarOrConst> variables) {
		final var newStates = mStates.stream().map(s -> new SingleStateRecord<>(s.state().addVariables(variables),
				s.threadCounter(), s.abstractLocationState())).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> removeVariables(
			final Collection<IProgramVarOrConst> variables) {
		final var newStates = mStates.stream().map(s -> new SingleStateRecord<>(s.state().removeVariables(variables),
				s.threadCounter(), s.abstractLocationState())).collect(Collectors.toSet());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, newStates);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mStates.stream().anyMatch(s -> s.state().getVariables().contains(var));
	}

	@Override
	public ImmutableSet<IProgramVarOrConst> getVariables() {
		final var allVars = mStates.stream().flatMap(s -> s.state().getVariables().stream())
				.collect(Collectors.toSet());
		return ImmutableSet.of(allVars);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> union(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		final Set<SingleStateRecord<STATE, LOC>> combined = new HashSet<>(mStates);
		combined.addAll(other.getStates());
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, reduceByEquality(combined));
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> intersect(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		final var first = getSingleState();
		final var second = other.getSingleState();
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, 999,
				Set.of(new SingleStateRecord<>(first.state().intersect(second.state()),
						first.threadCounter().intersect(second.threadCounter()),
						first.abstractLocationState().intersect(second.abstractLocationState()))));
	}

	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> crossProduct(
			final BiFunction<SingleStateRecord<STATE, LOC>, SingleStateRecord<STATE, LOC>, SingleStateRecord<STATE, LOC>> combiner,
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other, final int maxSize) {
		final Set<SingleStateRecord<STATE, LOC>> newSet = new HashSet<>(mStates.size() * other.getStates().size());
		for (final SingleStateRecord<STATE, LOC> stLeft : mStates) {
			for (final SingleStateRecord<STATE, LOC> stRight : other.getStates()) {
				final SingleStateRecord<STATE, LOC> combined = combiner.apply(stLeft, stRight);
				if (!combined.state().isBottom()) {
					newSet.add(combined);
				}
			}
		}
		final Set<SingleStateRecord<STATE, LOC>> reduced = reduce(newSet, maxSize);
		if (reduced.equals(mStates)) {
			return this;
		}
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, maxSize, reduced);
	}

	private static <STATE extends IAbstractState<STATE>, LOC extends IcfgLocation> Set<SingleStateRecord<STATE, LOC>> reduce(
			final Set<SingleStateRecord<STATE, LOC>> states, final int maxSize) {

		if (states.size() <= maxSize) {
			return states;
		}
		// Example: simply keep the first maxSize elements, discarding extras
		// In a real version, do something like the “ordered merge” or “maximal elements” logic
		return states.stream().limit(maxSize).collect(Collectors.toSet());
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> patch(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> dominator) {
		return crossProduct((left, right) -> {
			final STATE patchedState = left.state().patch(right.state());
			// TODO: just using dominators threadcounter/abstractlocation sound?
			return new SingleStateRecord<>(patchedState, left.threadCounter(), left.abstractLocationState());
		}, dominator, mStates.size() * dominator.getStates().size());
	}

	@Override
	public boolean isEmpty() {
		return mStates.stream().allMatch(s -> s.state().isEmpty());
	}

	@Override
	public boolean isBottom() {
		return mStates.stream().allMatch(s -> s.state().isBottom());
	}

	// TODO: also look at threadcounter and abstractlocations ?
	@Override
	public boolean isEqualTo(final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		if (other == null) {
			return false;
		}
		if (!other.getVariables().equals(getVariables())) {
			return false;
		}
		for (final SingleStateRecord<STATE, LOC> state : mStates) {
			final boolean found = other.getStates().stream().anyMatch(state::equals);
			if (!found) {
				return false;
			}
		}
		return true;
	}

	@Override
	public SubsetResult isSubsetOf(final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		// TODO: Is this sound?
		if (getSingleState() == null) {
			return SubsetResult.STRICT;
		} else if (other.getSingleState() == null) {
			return SubsetResult.NONE;
		}
		return getSingleState().state().isSubsetOf(other.getSingleState().state());
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> compact() {
		final Set<SingleStateRecord<STATE, LOC>> c = new HashSet<>(mStates.size());
		final Set<IProgramVarOrConst> vars = new HashSet<>();
		for (final SingleStateRecord<STATE, LOC> st : mStates) {
			final STATE comp = st.state().compact();
			c.add(new SingleStateRecord<>(comp, st.threadCounter(), st.abstractLocationState()));
			vars.addAll(comp.getVariables());
		}
		if (c.equals(mStates)) {
			return this;
		}
		final Set<SingleStateRecord<STATE, LOC>> sync = new HashSet<>(c.size());
		for (final SingleStateRecord<STATE, LOC> st : c) {
			final Set<IProgramVarOrConst> missing = new HashSet<>(vars);
			missing.removeAll(st.state().getVariables());
			if (missing.isEmpty()) {
				sync.add(st);
			} else {
				sync.add(new SingleStateRecord<>(st.state().addVariables(missing), st.threadCounter(),
						st.abstractLocationState()));
			}
		}
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, sync);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> renameVariables(
			final Map<IProgramVarOrConst, IProgramVarOrConst> old2new) {
		final Set<SingleStateRecord<STATE, LOC>> renamed = mStates.stream().map(st -> {
			final STATE r = st.state().renameVariables(old2new);
			return new SingleStateRecord<>(r, st.threadCounter(), st.abstractLocationState());
		}).collect(Collectors.toSet());
		if (renamed.equals(mStates)) {
			return this;
		}
		return new GuardedInterferenceDomainStateDisj<>(mUnderlying, MAXSIZE, renamed);
	}

	@Override
	public Term getTerm(final Script script) {
		final Set<Term> terms = mStates.stream().map(st -> st.state().getTerm(script)).collect(Collectors.toSet());
		return SmtUtils.or(script, terms);
	}

	@Override
	public String toLogString() {
		return mStates.stream().map(s -> s.state().toString() + " | " + s.threadCounter().toString() + " | "
				+ s.abstractLocationState().toString()).collect(Collectors.joining("\n")) + "\n";
	}

	@Override
	public String toString() {
		return mStates.toString();
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> apply(
			final IAbstractDomain<STATE, ACTION> underlyingDomain,
			final IAbstractPostOperator<STATE, ACTION> underlyingPostOp, final ACTION transition) {
		final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> postRelationalState = new GuardedInterferenceDomainStateDisj<>(
				underlyingDomain, MAXSIZE,
				this.getStates().stream()
						.flatMap(s -> underlyingPostOp.apply(s.state(), transition).stream().filter(a -> !a.isBottom())
								.map(newState -> new SingleStateRecord<STATE, LOC>(newState, s.threadCounter(),
										s.abstractLocationState().copyToNewState(transition.getTarget()))))
						.collect(Collectors.toSet()));
		return postRelationalState;
	}

}
