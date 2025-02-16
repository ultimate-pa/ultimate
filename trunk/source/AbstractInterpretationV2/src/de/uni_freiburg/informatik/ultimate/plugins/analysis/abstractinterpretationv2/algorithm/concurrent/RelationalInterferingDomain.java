package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Wrapper for an {@code IAbstractDomain} with a different post-operator to consider interferences, just like
 * {@code InterferingDomain}. Underlying domain is SIFA domain. Domain also inlcudes Threadinformation.
 */
public class RelationalInterferingDomain implements IAbstractDomain<RelationalInterferingState, IcfgEdge> {
	private final IDomain mUnderlying;
	private final String mCurrentThreadName;
	private final RelationalInterferingPostOperator mRelInterferingPostOperator;
	private final RelationalInterferingStateFactoryAndPredicateHelper mStateFactory;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;

	// through the symboltable we already have an (inverse) mapping of (programVar) x <-> (TermVar) x
	// we use this additional map to save (termvar) x'.
	// so no hashrelation needed ?
	private final PrimedTermvariableHelper mPrimedVarMap;
	private final RelationalInterferenceState mInterferences;

	public RelationalInterferingDomain(final IIcfg<?> cfg, final IDomain underlying,
			final BasicPredicateFactory predicateFactory, final IUltimateServiceProvider serviceProvider) {
		mThreadInstanceCounterFactory = new ThreadInstanceCounterFactory(cfg);
		mPrimedVarMap = new PrimedTermvariableHelper(cfg, serviceProvider);
		mInterferences = new RelationalInterferenceState(cfg.getCfgSmtToolkit().getManagedScript());
		mUnderlying = underlying;
		mStateFactory = new RelationalInterferingStateFactoryAndPredicateHelper(serviceProvider, cfg.getCfgSmtToolkit(),
				mUnderlying, this, predicateFactory, mInterferences, threadInstanceCounterFactory());
		mCurrentThreadName = cfg.getCfgSmtToolkit().getProcedures().iterator().next();
		mRelInterferingPostOperator = new RelationalInterferingPostOperator(mUnderlying, mCurrentThreadName, mStateFactory,
				cfg, serviceProvider, mInterferences, mPrimedVarMap);
	}

	public ThreadInstanceCounterFactory threadInstanceCounterFactory() {
		return mThreadInstanceCounterFactory;
	}

	public RelationalInterferenceState interferenceState() {
		return mInterferences;
	}

	@Override
	public RelationalInterferingState createTopState() {
		return mStateFactory.getTopState();
	}

	@Override
	public RelationalInterferingState createBottomState() {
		return mStateFactory.getBottomState();
	}

	public RelationalInterferingState createBottomPreconditionState() {
		return mStateFactory.getBottomPreconditionState();
	}

	@Override
	public IAbstractStateBinaryOperator<RelationalInterferingState> getWideningOperator() {
		return new RelationalInterferingWideningOperator(mUnderlying, threadInstanceCounterFactory(), mStateFactory);
	}

	@Override
	public IAbstractPostOperator<RelationalInterferingState, IcfgEdge> getPostOperator() {
		return mRelInterferingPostOperator;
	}

	@Override
	public String domainDescription() {
		return "SIFA - " + mUnderlying.toString() + " with interferences";
	}
}
