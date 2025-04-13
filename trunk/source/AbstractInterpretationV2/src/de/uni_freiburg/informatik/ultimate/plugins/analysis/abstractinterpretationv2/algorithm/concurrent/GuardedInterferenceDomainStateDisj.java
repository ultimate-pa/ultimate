package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public final class GuardedInterferenceDomainStateDisj<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractState<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> {
	private final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> mDisjState;
	private final GuardedInterferenceDomainStateFactory<STATE, ACTION, LOC> mFactory;
	private final int MAXSIZE;
	public static int maxSizeReached = 0;

	public GuardedInterferenceDomainStateDisj(final IAbstractDomain<STATE, ACTION> underlying,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj,
			final int maxsize) {
		mDisjState = DisjunctiveAbstractState.createDisjunction(reduceBySameTracking(disj.getStates()), maxsize);
		mFactory = new GuardedInterferenceDomainStateFactory<>(underlying);
		MAXSIZE = maxsize;
		updateMax(mDisjState.getStates().size());
	}

	public GuardedInterferenceDomainStateDisj(final GuardedInterferenceDomainStateFactory<STATE, ACTION, LOC> factory,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj,
			final int maxsize) {
		mDisjState = DisjunctiveAbstractState.createDisjunction(reduceBySameTracking(disj.getStates()), maxsize);
		mFactory = factory;
		MAXSIZE = maxsize;
		updateMax(mDisjState.getStates().size());
	}

	public GuardedInterferenceDomainStateDisj(final IAbstractDomain<STATE, ACTION> underlying,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj, final int maxsize) {
		mDisjState = DisjunctiveAbstractState.createDisjunction(reduceBySameTracking(disj), maxsize);
		mFactory = new GuardedInterferenceDomainStateFactory<>(underlying);
		MAXSIZE = maxsize;
		updateMax(mDisjState.getStates().size());
	}

	public GuardedInterferenceDomainStateDisj(final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		mDisjState = other.mDisjState;
		mFactory = other.mFactory;
		MAXSIZE = other.MAXSIZE;
		updateMax(mDisjState.getStates().size());
	}

	public void updateMax(final int newMax) {
		if (newMax > maxSizeReached) {
			maxSizeReached = newMax;
		}
		if (newMax >= 35) {
			maxSizeReached = newMax;
		}
	}

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> getDisjunctiveAbstractState() {
		return mDisjState;
	}

	public int maxSize() {
		return MAXSIZE;
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> getReduced() {
		return reduceBySameTracking(mDisjState.getStates());

	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> reduceBySameTracking(
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states) {
		if (states.size() <= 1) {
			return states;
		}
		final List<GuardedInterferenceDomainState<STATE, ACTION, LOC>> toProcess = new ArrayList<>(states);
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result = new HashSet<>();
		final int startingLen = toProcess.size();

		while (!toProcess.isEmpty()) {
			GuardedInterferenceDomainState<STATE, ACTION, LOC> base = toProcess.remove(toProcess.size() - 1);
			final ListIterator<GuardedInterferenceDomainState<STATE, ACTION, LOC>> it = toProcess.listIterator();
			while (it.hasNext()) {
				final GuardedInterferenceDomainState<STATE, ACTION, LOC> candidate = it.next();
				if (base.equalThreadTracking(candidate)) {
					base = base.union(candidate);
					it.remove();
				}
			}
			result.add(base);
		}
		final int endLen = result.size();
		return result;
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames) {
		final var disj = DisjunctiveAbstractState.createDisjunction(
				mFactory.initializeLocation(location, globalMap, threadNames, mDisjState.getStates()), MAXSIZE);
		return new GuardedInterferenceDomainStateDisj<>(mFactory, disj, MAXSIZE);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames, final Set<LOC> forkLocs) {
		final var disj = DisjunctiveAbstractState.createDisjunction(
				mFactory.initializeLocation(location, globalMap, threadNames, forkLocs, mDisjState.getStates()),
				MAXSIZE);
		return new GuardedInterferenceDomainStateDisj<>(mFactory, disj, MAXSIZE);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> movedTo(final String threadName,
			final int newLocation) {
		final var disj = DisjunctiveAbstractState
				.createDisjunction(mFactory.movedTo(threadName, newLocation, mDisjState.getStates()), MAXSIZE);
		return new GuardedInterferenceDomainStateDisj<>(mFactory, disj, MAXSIZE);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> setThreadsActive(
			final Collection<String> forkingStrings) {
		final var disj = DisjunctiveAbstractState
				.createDisjunction(mFactory.setThreadsActive(forkingStrings, mDisjState.getStates()), MAXSIZE);
		return new GuardedInterferenceDomainStateDisj<>(mFactory, disj, MAXSIZE);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> setThreadsInf(
			final Collection<String> forkingStrings) {
		final var disj = DisjunctiveAbstractState
				.createDisjunction(mFactory.setThreadsInf(forkingStrings, mDisjState.getStates()), MAXSIZE);
		return new GuardedInterferenceDomainStateDisj<>(mFactory, disj, MAXSIZE);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> incrementThread(final String thread) {
		final var disj = DisjunctiveAbstractState
				.createDisjunction(mFactory.incrementThread(thread, mDisjState.getStates()), MAXSIZE);
		return new GuardedInterferenceDomainStateDisj<>(mFactory, disj, MAXSIZE);
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> apply(
			final IAbstractPostOperator<STATE, ACTION> underlyingPostOp, final ACTION transition) {
		final var disj = DisjunctiveAbstractState
				.createDisjunction(mFactory.apply(underlyingPostOp, transition, mDisjState.getStates()), MAXSIZE);
		return new GuardedInterferenceDomainStateDisj<>(mFactory, disj, MAXSIZE);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> addVariable(final IProgramVarOrConst variable) {
		return new GuardedInterferenceDomainStateDisj<>(mFactory, mDisjState.addVariable(variable), MAXSIZE);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> removeVariable(final IProgramVarOrConst variable) {
		return new GuardedInterferenceDomainStateDisj<>(mFactory, mDisjState.removeVariable(variable), MAXSIZE);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> addVariables(
			final Collection<IProgramVarOrConst> variables) {
		return new GuardedInterferenceDomainStateDisj<>(mFactory, mDisjState.addVariables(variables), MAXSIZE);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> removeVariables(
			final Collection<IProgramVarOrConst> variables) {
		return new GuardedInterferenceDomainStateDisj<>(mFactory, mDisjState.removeVariables(variables), MAXSIZE);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mDisjState.containsVariable(var);
	}

	@Override
	public ImmutableSet<IProgramVarOrConst> getVariables() {
		return mDisjState.getVariables();
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> renameVariables(
			final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		return new GuardedInterferenceDomainStateDisj<>(mFactory, mDisjState.renameVariables(old2newVars), MAXSIZE);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> patch(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> dominator) {
		return new GuardedInterferenceDomainStateDisj<>(mFactory, mDisjState.patch(dominator.mDisjState), MAXSIZE);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> intersect(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		return new GuardedInterferenceDomainStateDisj<>(mFactory, mDisjState.intersect(other.mDisjState), MAXSIZE);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> union(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> rawUnion = mDisjState
				.union(other.mDisjState);
		final var newdisj = DisjunctiveAbstractState.createDisjunction(reduceBySameTracking(rawUnion.getStates()),
				MAXSIZE);

		return new GuardedInterferenceDomainStateDisj<>(mFactory, newdisj, MAXSIZE);
	}

	@Override
	public boolean isEmpty() {
		return mDisjState.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mDisjState.isBottom();
	}

	public boolean isStateBottom() {
		return mDisjState.getStates().stream().allMatch(s -> s.isStateBottom());
	}

	@Override
	public boolean isEqualTo(final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		return mDisjState.isEqualTo(other.mDisjState);
	}

	@Override
	public SubsetResult isSubsetOf(final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> other) {
		return mDisjState.isSubsetOf(other.mDisjState);
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> compact() {
		return new GuardedInterferenceDomainStateDisj<>(mFactory, mDisjState.compact(), MAXSIZE);
	}

	@Override
	public Term getTerm(final Script script) {
		return mDisjState.getTerm(script);
	}

	@Override
	public String toLogString() {
		return mDisjState.toLogString();
	}

	@Override
	public String toString() {
		return mDisjState.toLogString();
	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> getSingleState() {
		final var states = mDisjState.getStates();
		if (states.isEmpty()) {
			return null;
		}
		final var it = states.iterator();
		GuardedInterferenceDomainState<STATE, ACTION, LOC> merged = it.next();
		while (it.hasNext()) {
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> next = it.next();
			final STATE mergedState = merged.state().union(next.state());
			final ThreadInstanceCounter mergedThreads = merged.threadCounter().union(next.threadCounter());
			final AbstractLocationState<LOC> mergedLocation = merged.abstractLocationState()
					.union(next.abstractLocationState());
			merged = new GuardedInterferenceDomainState<>(mergedState, mergedThreads, mergedLocation);
		}
		return merged;
	}

	public ThreadInstanceCounter getThreadInstanceState() {
		return getSingleState().threadCounter();
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> getStates() {
		return mDisjState.getStates();
	}

}
