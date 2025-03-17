package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public final class GuardedInterferenceDomainState<STATE extends IAbstractState<STATE>, ACTION>
		implements IAbstractState<GuardedInterferenceDomainState<STATE, ACTION>> {

	private final IAbstractDomain<STATE, ACTION> mUnderlying;

	private final STATE mState;
	private final ThreadInstanceCounter mThreadInstanceCounter;

	public GuardedInterferenceDomainState(final IAbstractDomain<STATE, ACTION> underlying, final STATE state,
			final ThreadInstanceCounter threadcounter) {
		mUnderlying = underlying;
		mState = state.union(underlying.createBottomState().addVariables(state.getVariables()));
		mThreadInstanceCounter = new ThreadInstanceCounter(threadcounter);
	}

	public GuardedInterferenceDomainState(final IAbstractDomain<STATE, ACTION> underlying, final Collection<STATE> states,
			final ThreadInstanceCounter threadcounter) {
		mUnderlying = underlying;
		STATE unionState = null;
		// TODO:Maybe use disjunctiveabstractstate instead?
		if (!states.isEmpty()) {
			unionState = states.iterator().next();
		}

		for (final STATE state : states) {
			// unionState = FixpointEngineConcurrentUtils.unionOnSharedVariables(unionState,
			// state);
			unionState = unionState.union(state);
		}
		if (unionState == null) {
			mState = underlying.createBottomState();
		} else {
			mState = unionState;
		}
		mThreadInstanceCounter = new ThreadInstanceCounter(threadcounter);
	}

	public STATE getStateCopy() {
		return mState;
	}

	public GuardedInterferenceDomainState<STATE, ACTION> setThreadsActive(final Collection<String> forkingStrings) {
		final var newThreadcounter = new ThreadInstanceCounter(mThreadInstanceCounter.setActive(forkingStrings));
		return new GuardedInterferenceDomainState<>(mUnderlying, getStateCopy(), newThreadcounter);
	}

	public GuardedInterferenceDomainState<STATE, ACTION> setThreadsInf(final Collection<String> forkingStrings) {
		final var newThreadcounter = new ThreadInstanceCounter(mThreadInstanceCounter.setInf(forkingStrings));
		return new GuardedInterferenceDomainState<>(mUnderlying, getStateCopy(), newThreadcounter);
	}

	public ThreadInstanceCounter getThreadInstanceState() {
		return mThreadInstanceCounter;
	}

	public GuardedInterferenceDomainState<STATE, ACTION> incrementThread(final String thread) {
		final var newThreadcounter = mThreadInstanceCounter.incrementThread(thread);
		return new GuardedInterferenceDomainState<>(mUnderlying, getStateCopy(), newThreadcounter);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION> addVariable(final IProgramVarOrConst variable) {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.addVariable(variable), mThreadInstanceCounter);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION> removeVariable(final IProgramVarOrConst variable) {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.removeVariable(variable), mThreadInstanceCounter);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION> addVariables(final Collection<IProgramVarOrConst> variables) {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.addVariables(variables), mThreadInstanceCounter);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION> removeVariables(final Collection<IProgramVarOrConst> variables) {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.removeVariables(variables), mThreadInstanceCounter);
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
	public GuardedInterferenceDomainState<STATE, ACTION> patch(final GuardedInterferenceDomainState<STATE, ACTION> dominator) {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.patch(dominator.getStateCopy()),
				mThreadInstanceCounter);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION> intersect(final GuardedInterferenceDomainState<STATE, ACTION> other) {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.intersect(other.getStateCopy()),
				mThreadInstanceCounter.intersect(other.getThreadInstanceState()));
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION> union(final GuardedInterferenceDomainState<STATE, ACTION> other) {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.union(other.getStateCopy()),
				mThreadInstanceCounter.union(other.getThreadInstanceState()));
	}

	@Override
	public boolean isEmpty() {
		return mState.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mState.isBottom();
	}

	@Override
	public boolean isEqualTo(final GuardedInterferenceDomainState<STATE, ACTION> other) {
		return isSubsetOf(other) == SubsetResult.NON_STRICT && other.isSubsetOf(this) == SubsetResult.NON_STRICT;
	}

	@Override
	public SubsetResult isSubsetOf(final GuardedInterferenceDomainState<STATE, ACTION> other) {
		return mState.isSubsetOf(other.getStateCopy());
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION> compact() {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.compact(), mThreadInstanceCounter);
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION>
			renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		return new GuardedInterferenceDomainState<>(mUnderlying, mState.renameVariables(old2newVars),
				mThreadInstanceCounter);
	}

	@Override
	public Term getTerm(final Script script) {
		return mState.getTerm(script);
	}

	@Override
	public String toLogString() {
		return mState.toString() + mThreadInstanceCounter.getThreadInstances().toString();
	}

	@Override
	public String toString() {
		if (mState == null) {
			return "null";
		}
		return mState.toString() + mThreadInstanceCounter.getThreadInstances().toString();
	}
}
