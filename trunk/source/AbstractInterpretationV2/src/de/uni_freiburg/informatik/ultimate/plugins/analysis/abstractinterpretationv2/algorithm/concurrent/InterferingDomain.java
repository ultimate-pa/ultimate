package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;

public class InterferingDomain<STATE extends IAbstractState<STATE>, ACTION, LOC>
		implements IAbstractDomain<STATE, ACTION> {
	private final IAbstractDomain<STATE, ACTION> mUnderlying;
	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final Map<LOC, DisjunctiveAbstractState<STATE>> mInterferences;

	public InterferingDomain(final IAbstractDomain<STATE, ACTION> underlying,
			final ITransitionProvider<ACTION, LOC> transitionProvider,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		mUnderlying = underlying;
		mTransitionProvider = transitionProvider;
		mInterferences = interferences;
	}

	@Override
	public STATE createTopState() {
		return mUnderlying.createTopState();
	}

	@Override
	public STATE createBottomState() {
		return mUnderlying.createBottomState();
	}

	@Override
	public IAbstractStateBinaryOperator<STATE> getWideningOperator() {
		return mUnderlying.getWideningOperator();
	}

	@Override
	public void beforeFixpointComputation(final Object... objects) {
		mUnderlying.beforeFixpointComputation(objects);
	}

	@Override
	public IAbstractPostOperator<STATE, ACTION> getPostOperator() {
		return new InterferingPostOperator<>(mTransitionProvider, mInterferences, mUnderlying.getPostOperator());
	}

	@Override
	public boolean isAbstractable(final Term term) {
		return mUnderlying.isAbstractable(null);
	}

	@Override
	public <LOC2> void afterFixpointComputation(final IAbstractInterpretationResult<STATE, ACTION, LOC2> result) {
		mUnderlying.afterFixpointComputation(result);
	}

	@Override
	public String domainDescription() {
		return mUnderlying.domainDescription() + " with interferences";
	}
}
