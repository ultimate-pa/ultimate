/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * IHoareTripleChecker that caches already computed results. Also tries to use these results for more intelligent
 * checks.
 *
 * @author Matthias Heizmann
 *
 */
public abstract class CachingHoareTripleChecker implements IHoareTripleChecker {

	protected static final boolean UNKNOWN_IF_SOME_EXTENDED_CHECK_IS_UNKNOWN = true;

	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;
	protected final IHoareTripleChecker mComputingHoareTripleChecker;
	protected final IPredicateUnifier mPredicateUnifer;

	private final InCaReCounter mResultFromSolver = new InCaReCounter();
	private final InCaReCounter mResultFromCache = new InCaReCounter();
	private final InCaReCounter mResultFromExtendedCacheCheck = new InCaReCounter();

	private final NestedMap3<IAction, IPredicate, IPredicate, Validity> mInternalCache;
	private final NestedMap3<IAction, IPredicate, IPredicate, Validity> mCallCache;
	private final Map<IPredicate, NestedMap3<IAction, IPredicate, IPredicate, Validity>> mReturnCache;

	public CachingHoareTripleChecker(final IUltimateServiceProvider services,
			final IHoareTripleChecker protectedHoareTripleChecker, final IPredicateUnifier predicateUnifer) {
		this(services, protectedHoareTripleChecker, predicateUnifer, new NestedMap3<>(), new NestedMap3<>(),
				new HashMap<>());
	}

	public CachingHoareTripleChecker(final IUltimateServiceProvider services,
			final IHoareTripleChecker protectedHoareTripleChecker, final IPredicateUnifier predicateUnifer,
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> initialInternalCache,
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> initialCallCache,
			final Map<IPredicate, NestedMap3<IAction, IPredicate, IPredicate, Validity>> initialReturnCache) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mComputingHoareTripleChecker = Objects.requireNonNull(protectedHoareTripleChecker);
		mPredicateUnifer = Objects.requireNonNull(predicateUnifer);
		mInternalCache = Objects.requireNonNull(initialInternalCache);
		mCallCache = Objects.requireNonNull(initialCallCache);
		mReturnCache = Objects.requireNonNull(initialReturnCache);
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		Validity result = getFromInternalCache(pre, act, succ);
		if (result == null) {
			result = extendedBinaryCacheCheck(pre, act, succ, mInternalCache);
			if (result == null) {
				result = mComputingHoareTripleChecker.checkInternal(pre, act, succ);
				mResultFromSolver.incIn();
			} else {
				mResultFromExtendedCacheCheck.incIn();
			}
			addToInternalCache(pre, act, succ, result);
		} else {
			mResultFromCache.incIn();
		}
		return result;
	}

	private Validity getFromInternalCache(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		return mInternalCache.get(act, pre, succ);
	}

	private final void addToInternalCache(final IPredicate pre, final IInternalAction act, final IPredicate succ,
			final Validity result) {
		mInternalCache.put(act, pre, succ, result);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		Validity result = getFromCallCache(pre, act, succ);
		if (result == null) {
			result = extendedBinaryCacheCheck(pre, act, succ, mCallCache);
			if (result == null) {
				result = mComputingHoareTripleChecker.checkCall(pre, act, succ);
				mResultFromSolver.incCa();
			} else {
				mResultFromExtendedCacheCheck.incCa();
			}
			addToCallCache(pre, act, succ, result);
		} else {
			mResultFromCache.incCa();
		}
		return result;
	}

	private Validity getFromCallCache(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		return mCallCache.get(act, pre, succ);
	}

	private final void addToCallCache(final IPredicate pre, final ICallAction act, final IPredicate succ,
			final Validity result) {
		mCallCache.put(act, pre, succ, result);
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		Validity result = getFromReturnCache(preLin, preHier, act, succ);
		if (result == null) {
			if (!mReturnCache.containsKey(preHier)) {
				mReturnCache.put(preHier, new NestedMap3<>());
			}
			result = extendedBinaryCacheCheck(preLin, act, succ, mReturnCache.get(preHier));
			if (result == null) {
				result = mComputingHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
				mResultFromSolver.incRe();
			} else {
				mResultFromExtendedCacheCheck.incRe();
			}
			addToReturnCache(preLin, preHier, act, succ, result);
		} else {
			mResultFromCache.incRe();
		}
		return result;
	}

	private Validity getFromReturnCache(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		final NestedMap3<IAction, IPredicate, IPredicate, Validity> map = mReturnCache.get(preHier);
		if (map == null) {
			return null;
		}
		return map.get(act, preLin, succ);

	}

	private final void addToReturnCache(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ, final Validity result) {
		NestedMap3<IAction, IPredicate, IPredicate, Validity> map = mReturnCache.get(preHier);
		if (map == null) {
			map = new NestedMap3<>();
			mReturnCache.put(preHier, map);
		}
		map.put(act, preLin, succ, result);
	}

	protected abstract Validity extendedBinaryCacheCheck(final IPredicate pre, final IAction act, final IPredicate succ,
			NestedMap3<IAction, IPredicate, IPredicate, Validity> binaryCache);

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mComputingHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	public IHoareTripleChecker getProtectedHoareTripleChecker() {
		return mComputingHoareTripleChecker;
	}

	@Override
	public void releaseLock() {
		mComputingHoareTripleChecker.releaseLock();
	}

}
