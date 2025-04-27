package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class GuardedInterferenceDomainState<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> {
	private final STATE mState;
	private final ThreadInstanceCounter mThreadCounter;
	private final AbstractLocationState<LOC> mAbstractLocationState;

	public GuardedInterferenceDomainState(final STATE state, final ThreadInstanceCounter threadCounter,
			final AbstractLocationState<LOC> abstractLocationState) {
		mState = state;
		mThreadCounter = threadCounter;
		mAbstractLocationState = abstractLocationState;
	}

	public STATE state() {
		return mState;
	}

	public ThreadInstanceCounter threadCounter() {
		return mThreadCounter;
	}

	public AbstractLocationState<LOC> abstractLocationState() {
		return mAbstractLocationState;
	}

	public boolean equalThreadTracking(final GuardedInterferenceDomainState<STATE, ACTION, LOC> other) {
		return mAbstractLocationState.equalThreadTracking(other.mAbstractLocationState);

	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames) {
		return new GuardedInterferenceDomainState<>(this.state(), this.threadCounter(),
				new AbstractLocationState<>(location, globalMap, threadNames));
	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> initWithGiven(final LOC location,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> other) {
		return new GuardedInterferenceDomainState<>(other.state(), other.threadCounter(),
				new AbstractLocationState<>(location, other.mAbstractLocationState));
	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames, final Set<LOC> forkLocs) {
		GuardedInterferenceDomainState<STATE, ACTION, LOC> newState = new GuardedInterferenceDomainState<>(this.state(),
				this.threadCounter(), new AbstractLocationState<>(location, globalMap, threadNames));
		for (final LOC loc : forkLocs) {
			newState = newState.movedTo(loc.getProcedure(), newState.abstractLocationState().getLocationMap()
					.getAbstractLocation((LOC) loc.getOutgoingNodes().iterator().next()));
		}
		return newState;
	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> movedTo(final String threadName, final int newLocation) {
		return new GuardedInterferenceDomainState<>(this.state(), this.threadCounter(),
				this.abstractLocationState().movedTo(threadName, newLocation));
	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> setThreadsActive(
			final Collection<String> forkingStrings) {
		final var newThreadcounter = new ThreadInstanceCounter(threadCounter().setActive(forkingStrings));
		return new GuardedInterferenceDomainState<>(this.state(), newThreadcounter, this.abstractLocationState());
	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> setThreadsInf(final Collection<String> forkingStrings) {
		final var newThreadcounter = new ThreadInstanceCounter(threadCounter().setInf(forkingStrings));
		return new GuardedInterferenceDomainState<>(this.state(), newThreadcounter, this.abstractLocationState());
	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> incrementThread(final String thread) {
		final var newThreadcounter = this.threadCounter().incrementThread(thread);
		return new GuardedInterferenceDomainState<>(this.state(), newThreadcounter, this.abstractLocationState());
	}

	public boolean isEqual(final GuardedInterferenceDomainState<STATE, ACTION, LOC> other) {
		if (!other.state().isEqualTo(this.state())) {
			return false;
		}
		if (!other.threadCounter().isEqualTo(this.threadCounter())) {
			return false;
		}
		if (!other.abstractLocationState().isEqualTo(this.abstractLocationState())) {
			return false;
		}
		return true;
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> addVariable(final IProgramVarOrConst variable) {
		return new GuardedInterferenceDomainState<>(mState.addVariable(variable), mThreadCounter,
				mAbstractLocationState);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> removeVariable(final IProgramVarOrConst variable) {
		return new GuardedInterferenceDomainState<>(mState.removeVariable(variable), mThreadCounter,
				mAbstractLocationState);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> addVariables(
			final Collection<IProgramVarOrConst> variables) {
		return new GuardedInterferenceDomainState<>(mState.addVariables(variables), mThreadCounter,
				mAbstractLocationState);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> removeVariables(
			final Collection<IProgramVarOrConst> variables) {
		return new GuardedInterferenceDomainState<>(mState.removeVariables(variables), mThreadCounter,
				mAbstractLocationState);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mState.containsVariable(var);
	}

	@Override
	public ImmutableSet<IProgramVarOrConst> getVariables() {
		return mState.getVariables();
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> renameVariables(
			final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		return new GuardedInterferenceDomainState<>(mState.renameVariables(old2newVars), mThreadCounter,
				mAbstractLocationState);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> patch(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> dominator) {
		return new GuardedInterferenceDomainState<>(mState.patch(dominator.state()), mThreadCounter,
				mAbstractLocationState);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> intersect(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> other) {
		return new GuardedInterferenceDomainState<>(mState.intersect(other.state()),
				mThreadCounter.intersect(other.threadCounter()),
				mAbstractLocationState.intersect(other.abstractLocationState()));
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> union(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> other) {
		return new GuardedInterferenceDomainState<>(mState.union(other.state()),
				mThreadCounter.union(other.threadCounter()),
				mAbstractLocationState.union(other.abstractLocationState()));
	}

	@Override
	public boolean isEmpty() {
		return mState.isEmpty();
	}

	// TODO: we gotta define unique bottom element, probably set loc and counter to bottom
	// when state bottom too ?
	// For now we are just saying any states with state().isBottom are the same. so "unique" bottom element this way
	@Override
	public boolean isBottom() {
		return state().isBottom();
	}

	public boolean isStateBottom() {
		return mState.isBottom();
	}

	@Override
	public boolean isEqualTo(final GuardedInterferenceDomainState<STATE, ACTION, LOC> other) {
		if (mState.isBottom() && other.mState.isBottom()) {
			return true;
		}
		if (!(other.state().isEqualTo(this.state()))) {
			return false;
		}
		if (!other.threadCounter().isEqualTo(threadCounter())) {
			return false;
		}
		if (!other.abstractLocationState().isEqualTo(this.abstractLocationState())) {
			return false;
		}
		return true;
	}

	@Override
	public SubsetResult isSubsetOf(final GuardedInterferenceDomainState<STATE, ACTION, LOC> other) {
		if (mState.isBottom() && other.mState.isBottom()) {
			return SubsetResult.EQUAL;
		}
		// TODO: maybe be less strict
		final SubsetResult stateResult = state().isSubsetOf(other.state());
		final var threadCounterResult = threadCounter().isSubsetOf(other.threadCounter());
		final var locationRestul = abstractLocationState().isSubsetOf(other.abstractLocationState());
		final var endResult = stateResult.min(threadCounterResult);

		return endResult.min(locationRestul);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> compact() {
		return new GuardedInterferenceDomainState<>(mState.compact(), mThreadCounter, mAbstractLocationState);
	}

	// TODO: include threadcounter, abstractloc as ghost variables ?
	@Override
	public Term getTerm(final Script script) {
		return mState.getTerm(script);
	}

	@Override
	public String toString() {
		return "- STATE:" + state().toString() + " COUNTER:" + threadCounter().toString() + " LOCATIONS:"
				+ abstractLocationState().toString();
	}

	@Override
	public String toLogString() {
		return "STATE:" + state().toString() + " | COUNTER:" + threadCounter().toString() + " | LOCATIONS:"
				+ abstractLocationState().toString();
	}

}
