package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class RelationalInterferingState<STATE extends IAbstractState<STATE>, ACTION>
		implements IAbstractState<RelationalInterferingState<STATE, ACTION>> {

	private final IAbstractDomain<STATE, ACTION> mUnderlying;

	private final STATE mState;
	private final ThreadInstanceCounter mThreadInstanceCounter;
	private final AbstractInterferenceState<STATE, ACTION> mInterferences;

	public RelationalInterferingState(final IAbstractDomain<STATE, ACTION> underlying, final STATE state,
			final ThreadInstanceCounter threadcounter, final AbstractInterferenceState<STATE, ACTION> interferences) {
		mUnderlying = underlying;
		mState = state.union(underlying.createBottomState().addVariables(state.getVariables()));
		mThreadInstanceCounter = new ThreadInstanceCounter(threadcounter);
		mInterferences = interferences;
	}

	public RelationalInterferingState(final IAbstractDomain<STATE, ACTION> underlying, final Collection<STATE> states,
			final ThreadInstanceCounter threadcounter, final AbstractInterferenceState<STATE, ACTION> interferences) {
		mUnderlying = underlying;
		STATE unionState = null;
		// TODO:Maybe use disjunctiveabstractstate instead?
		if (!states.isEmpty()) {
			unionState = states.iterator().next();
		}

		for (final STATE state : states) {
			// unionState = FixpointEngineConcurrentUtils.unionOnSharedVariables(unionState, state);
			unionState = unionState.union(state);
		}
		mState = unionState;
		mThreadInstanceCounter = new ThreadInstanceCounter(threadcounter);
		mInterferences = interferences;
	}

	// TODO
	public STATE getStateCopy() {
		return mState.union(mUnderlying.createBottomState().addVariables(mState.getVariables()));
	}

	public ThreadInstanceCounter getThreadInstanceState() {
		return mThreadInstanceCounter;
	}

	public RelationalInterferingState<STATE, ACTION> incrementThread(final String thread) {
		final var threadcounter = new ThreadInstanceCounter(mThreadInstanceCounter);
		threadcounter.incrementThread(thread);
		return new RelationalInterferingState<>(mUnderlying, getStateCopy(), threadcounter, mInterferences);
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> addVariable(final IProgramVarOrConst variable) {
		return new RelationalInterferingState<>(mUnderlying, mState.addVariable(variable), mThreadInstanceCounter,
				mInterferences);
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> removeVariable(final IProgramVarOrConst variable) {
		return new RelationalInterferingState<>(mUnderlying, mState.removeVariable(variable), mThreadInstanceCounter,
				mInterferences);
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> addVariables(final Collection<IProgramVarOrConst> variables) {
		return new RelationalInterferingState<>(mUnderlying, mState.addVariables(variables), mThreadInstanceCounter,
				mInterferences);
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> removeVariables(final Collection<IProgramVarOrConst> variables) {
		return new RelationalInterferingState<>(mUnderlying, mState.removeVariables(variables), mThreadInstanceCounter,
				mInterferences);
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
	public RelationalInterferingState<STATE, ACTION> patch(final RelationalInterferingState<STATE, ACTION> dominator) {
		return new RelationalInterferingState<>(mUnderlying, mState.patch(dominator.getStateCopy()),
				mThreadInstanceCounter, mInterferences);
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> intersect(final RelationalInterferingState<STATE, ACTION> other) {
		return new RelationalInterferingState<>(mUnderlying, mState.intersect(other.getStateCopy()),
				mThreadInstanceCounter.intersect(other.getThreadInstanceState()), mInterferences);
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> union(final RelationalInterferingState<STATE, ACTION> other) {
		return new RelationalInterferingState<>(mUnderlying, mState.union(other.getStateCopy()),
				mThreadInstanceCounter.union(other.getThreadInstanceState()), mInterferences);
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
	public boolean isEqualTo(final RelationalInterferingState<STATE, ACTION> other) {
		return isSubsetOf(other) == SubsetResult.NON_STRICT && other.isSubsetOf(this) == SubsetResult.NON_STRICT;
	}

	@Override
	public SubsetResult isSubsetOf(final RelationalInterferingState<STATE, ACTION> other) {
		return mState.isSubsetOf(other.getStateCopy());
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> compact() {
		return new RelationalInterferingState<>(mUnderlying, mState.compact(), mThreadInstanceCounter, mInterferences);
	}

	@Override
	public RelationalInterferingState<STATE, ACTION>
			renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		return new RelationalInterferingState<>(mUnderlying, mState.renameVariables(old2newVars),
				mThreadInstanceCounter, mInterferences);
	}

	@Override
	public Term getTerm(final Script script) {
		return mState.getTerm(script);
	}

	@Override
	public String toLogString() {
		return mState.toString() + mThreadInstanceCounter.getThreadInstances().toString()
				+ mInterferences.interferenceStrings();
	}

	@Override
	public String toString() {
		return mState.toString() + mThreadInstanceCounter.getThreadInstances().toString()
				+ mInterferences.interferenceStrings();
	}
}
