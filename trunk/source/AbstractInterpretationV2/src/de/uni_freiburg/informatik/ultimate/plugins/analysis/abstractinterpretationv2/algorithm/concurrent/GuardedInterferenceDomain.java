package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Wrapper for an {@code IAbstractDomain} with a different post-operator to consider interferences, just like
 * {@code InterferingDomain}. Underlying domain is SIFA domain. Domain also inlcudes Threadinformation.
 */
public class GuardedInterferenceDomain<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractDomain<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION> mGuardedInterferenceDomainPostOperator;
	private final IAbstractStateBinaryOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> mWideningOperator;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;

	private final AbstractInterferenceState<STATE, ACTION, LOC> mInterferences;
	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	private final Map<String, ? extends LOC> mEntryLocs;
	AtomicInteger counter = new AtomicInteger();

	public GuardedInterferenceDomain(final IIcfg<? extends LOC> cfg, final IAbstractDomain<STATE, ACTION> underlying,
			final ILogger logger, final String locationAbstraction) {
		mThreadInstanceCounterFactory = new ThreadInstanceCounterFactory(cfg);
		mInterferences = new AbstractInterferenceState<>(cfg.getCfgSmtToolkit().getProcedures());

		mUnderlyingDomain = underlying;
		mEntryLocs = cfg.getProcedureEntryNodes();
		mAbstractLocationMap = switch (locationAbstraction) {
		case "Singleton" -> new AbstractLocationMap<>((l -> 1), mEntryLocs);
		case "Fully precise" -> new AbstractLocationMap<>((l -> counter.getAndIncrement()), mEntryLocs);
		case "Heuristic splitting" -> new AbstractLocationMap<>(l -> {
			final var incoming = l.getIncomingEdges();
			for (final IcfgEdge icfgEdge : incoming) {
				if (shouldDifferentiate(icfgEdge.getTransformula())) {
					return counter.getAndIncrement();
				}
			}
			return counter.get();
		}, mEntryLocs);
		default -> new AbstractLocationMap<>((l -> 1), mEntryLocs);
		};
		mGuardedInterferenceDomainPostOperator = new GuardedInterferenceDomainPostOperator<>(cfg, logger,
				mUnderlyingDomain, mUnderlyingDomain.getPostOperator(), this, mInterferences, mAbstractLocationMap);
		mWideningOperator = new GuardedInterferenceDomainWideningOperator<>(underlying, mThreadInstanceCounterFactory);
	}

	private static boolean shouldDifferentiate(final UnmodifiableTransFormula tf) {
		if (tf.isInfeasible() == UnmodifiableTransFormula.Infeasibility.INFEASIBLE) {
			return false;
		}
		if (!tf.getBranchEncoders().isEmpty()) {
			return true;
		}
		final Set<IProgramVar> assigned = tf.getAssignedVars();
		if (assigned.isEmpty()) {
			return true;
		}
//		if (assigned.size() > 1) {
//			return true;
//		}
		return false;
	}

	public AbstractLocationMap<LOC> getAbstractLocationMap() {
		return mAbstractLocationMap;
	}

	public IAbstractDomain<STATE, ACTION> getUnderlyingDomain() {
		return mUnderlyingDomain;
	}

	public ThreadInstanceCounterFactory threadInstanceCounterFactory() {
		return mThreadInstanceCounterFactory;
	}

	public AbstractInterferenceState<STATE, ACTION, LOC> interferenceState() {
		return mInterferences;
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> createTopState() {
		return new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, 999, mUnderlyingDomain.createTopState(),
				mThreadInstanceCounterFactory.createTopState());
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> createBottomState() {
		return new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, 999, mUnderlyingDomain.createBottomState(),
				mThreadInstanceCounterFactory.createBottomState());
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> createBottomPreconditionState() {
		return new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, 999, mUnderlyingDomain.createTopState(),
				mThreadInstanceCounterFactory.createBottomState());
	}

	@Override
	public IAbstractStateBinaryOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> getWideningOperator() {
		return mWideningOperator;
	}

	@Override
	public IAbstractPostOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION> getPostOperator() {
		return mGuardedInterferenceDomainPostOperator;
	}

	@Override
	public String domainDescription() {
		return "SIFA - " + mUnderlyingDomain.toString() + " with interferences";
	}

	@Override
	public void beforeFixpointComputation(final Object... objects) {
		mUnderlyingDomain.beforeFixpointComputation(objects);
	}

}
