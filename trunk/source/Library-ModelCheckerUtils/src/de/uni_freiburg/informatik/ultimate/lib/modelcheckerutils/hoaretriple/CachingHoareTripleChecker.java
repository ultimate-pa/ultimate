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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IterableIntersection;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * {@link IHoareTripleChecker} that caches already computed results. I also
 * utilizes the cache to do the following checks. Let us assume we want to check
 * the Hoare triple `{φ} st {ψ}`.
 * <li>If the cache contains a valid Hoare triple `{φ'} st {ψ'}` such that φ⇒φ'
 * and ψ'⇒ψ we return VALID.
 * <li>If the cache contains an invalid Hoare triple `{φ'} st {ψ'}` such that
 * φ'⇒φ and ψ⇒ψ' we return INVALID.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class CachingHoareTripleChecker implements IHoareTripleChecker {

	protected static final boolean UNKNOWN_IF_SOME_EXTENDED_CHECK_IS_UNKNOWN = false;

	private static final String UNKNOWN_CASE = "unknown case";
	private static final String CASE_MUST_NOT_OCCUR = "case must not occur";

	protected final ILogger mLogger;
	protected final IHoareTripleChecker mComputingHoareTripleChecker;
	protected final IPredicateUnifier mPredicateUnifier;

	private final InCaReCounter mResultFromSolver = new InCaReCounter();
	private final InCaReCounter mResultFromCache = new InCaReCounter();
	private final InCaReCounter mResultFromExtendedCacheCheck = new InCaReCounter();

	private final HoareTripleCheckerCache mCache;

	public CachingHoareTripleChecker(final IUltimateServiceProvider services,
			final IHoareTripleChecker computingHoareTripleChecker, final IPredicateUnifier predicateUnifer) {
		this(services, computingHoareTripleChecker, predicateUnifer, new HoareTripleCheckerCache());
	}

	public CachingHoareTripleChecker(final IUltimateServiceProvider services,
			final IHoareTripleChecker computingHoareTripleChecker, final IPredicateUnifier predicateUnifier,
			final HoareTripleCheckerCache initialCache) {
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mComputingHoareTripleChecker = Objects.requireNonNull(computingHoareTripleChecker);
		mPredicateUnifier = Objects.requireNonNull(predicateUnifier);
		mCache = Objects.requireNonNull(initialCache);
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		Validity result = mCache.getInternal(pre, act, succ);
		if (result == null) {
			result = extendedBinaryCacheCheck(pre, act, succ, mCache.getInternalCache());
			if (result == null) {
				result = mComputingHoareTripleChecker.checkInternal(pre, act, succ);
				mResultFromSolver.incIn();
			} else {
				mResultFromExtendedCacheCheck.incIn();
			}
			mCache.putInternal(pre, act, succ, result);
		} else {
			mResultFromCache.incIn();
		}
		return result;
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		Validity result = mCache.getCall(pre, act, succ);
		if (result == null) {
			result = extendedBinaryCacheCheck(pre, act, succ, mCache.getCallCache());
			if (result == null) {
				result = mComputingHoareTripleChecker.checkCall(pre, act, succ);
				mResultFromSolver.incCa();
			} else {
				mResultFromExtendedCacheCheck.incCa();
			}
			mCache.putCall(pre, act, succ, result);
		} else {
			mResultFromCache.incCa();
		}
		return result;
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		Validity result = mCache.getReturn(preLin, preHier, act, succ);
		if (result == null) {
			result = extendedReturnCacheCheck(preLin, preHier, act, succ, mCache.getReturnCache());
			if (result == null) {
				result = mComputingHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
				mResultFromSolver.incRe();
			} else {
				mResultFromExtendedCacheCheck.incRe();
			}
			mCache.putReturn(preLin, preHier, act, succ, result);
		} else {
			mResultFromCache.incRe();
		}
		return result;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mComputingHoareTripleChecker.getStatistics();
	}

	public IHoareTripleChecker getProtectedHoareTripleChecker() {
		return mComputingHoareTripleChecker;
	}

	@Override
	public void releaseLock() {
		mComputingHoareTripleChecker.releaseLock();
	}

	@Override
	public String toString() {
		return mComputingHoareTripleChecker.toString();
	}

	public HoareTripleCheckerCache getCache() {
		return mCache;
	}

	/**
	 * Cache check for internal actions and call actions. Both have only one
	 * predecessor and one successor.
	 */
	private Validity extendedBinaryCacheCheck(final IPredicate pre, final IAction act, final IPredicate succ,
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> binaryCache) {

		final NestedMap2<IPredicate, IPredicate, Validity> pred2succ = binaryCache.get(act);
		if (pred2succ == null) {
			// cache does not store information for our action
			return null;
		}

		boolean someResultWasUnknown = false;
		{
			final Set<IPredicate> strongerThanPre = mPredicateUnifier.getCoverageRelation().getCoveredPredicates(pre);
			final Set<IPredicate> weakerThanSucc = mPredicateUnifier.getCoverageRelation().getCoveringPredicates(succ);

			final Iterable<IPredicate> preds = new IterableIntersection<>(pred2succ.keySet(), strongerThanPre);
			for (final IPredicate strongP : preds) {
				final Map<IPredicate, Validity> succ2Val = pred2succ.get(strongP);
				final Iterable<IPredicate> succs = new IterableIntersection<>(succ2Val.keySet(), weakerThanSucc);
				for (final IPredicate weakS : succs) {
					final Validity validity = evaluteResultStrongerThanPreAndWeakerThanSucc(succ2Val.get(weakS));
					if (validity == null) {
						continue;
					}
					switch (validity) {
					case INVALID:
						return Validity.INVALID;
					case UNKNOWN:
						someResultWasUnknown = true;
						break;
					case NOT_CHECKED:
					case VALID:
						throw new AssertionError(CASE_MUST_NOT_OCCUR);
					default:
						throw new AssertionError(UNKNOWN_CASE);
					}
				}
			}
		}
		{
			final Set<IPredicate> weakerThanPre = mPredicateUnifier.getCoverageRelation().getCoveringPredicates(pre);
			final Set<IPredicate> strongerThanSucc = mPredicateUnifier.getCoverageRelation().getCoveredPredicates(succ);

			final Iterable<IPredicate> preds = new IterableIntersection<>(pred2succ.keySet(), weakerThanPre);
			for (final IPredicate weakP : preds) {
				final Map<IPredicate, Validity> succ2Val = pred2succ.get(weakP);
				final Iterable<IPredicate> succs = new IterableIntersection<>(succ2Val.keySet(), strongerThanSucc);
				for (final IPredicate strongS : succs) {
					final Validity validity = evaluteResultWeakerThanPreAndStrongerThanSucc(succ2Val.get(strongS));
					if (validity == null) {
						continue;
					}
					switch (validity) {
					case VALID:
						return Validity.VALID;
					case UNKNOWN:
						someResultWasUnknown = true;
						break;
					case NOT_CHECKED:
					case INVALID:
						throw new AssertionError(CASE_MUST_NOT_OCCUR);
					default:
						throw new AssertionError(UNKNOWN_CASE);
					}
				}
			}
		}
		if (UNKNOWN_IF_SOME_EXTENDED_CHECK_IS_UNKNOWN && someResultWasUnknown) {
			// we pass this result as a warning that the corresponding check might be
			// expensive
			return Validity.UNKNOWN;
		}
		return null;
	}

	protected Validity extendedReturnCacheCheck(final IPredicate preLin, final IPredicate preHier, final IAction act,
			final IPredicate succ,
			final NestedMap4<IAction, IPredicate, IPredicate, IPredicate, Validity> ternaryCache) {
		final NestedMap3<IPredicate, IPredicate, IPredicate, Validity> preHier2preLin2succ = ternaryCache.get(act);
		if (preHier2preLin2succ == null) {
			// cache does not store information for our action
			return null;
		}
		boolean someResultWasUnknown = false;
		{
			final Set<IPredicate> strongerThanPreHier = mPredicateUnifier.getCoverageRelation()
					.getCoveredPredicates(preHier);
			final Set<IPredicate> strongerThanPreLin = mPredicateUnifier.getCoverageRelation()
					.getCoveredPredicates(preLin);
			final Set<IPredicate> weakerThanSucc = mPredicateUnifier.getCoverageRelation().getCoveringPredicates(succ);

			final Iterable<IPredicate> predsHier = new IterableIntersection<>(preHier2preLin2succ.keySet(),
					strongerThanPreHier);
			for (final IPredicate strongPreHier : predsHier) {
				final NestedMap2<IPredicate, IPredicate, Validity> preLin2succ2Val = preHier2preLin2succ
						.get(strongPreHier);
				final Iterable<IPredicate> predsLin = new IterableIntersection<>(preLin2succ2Val.keySet(),
						strongerThanPreLin);
				for (final IPredicate strongPreLin : predsLin) {
					final Map<IPredicate, Validity> succ2Val = preLin2succ2Val.get(strongPreLin);
					final Iterable<IPredicate> succs = new IterableIntersection<>(succ2Val.keySet(), weakerThanSucc);
					for (final IPredicate weakS : succs) {
						final Validity validity = evaluteResultStrongerThanPreAndWeakerThanSucc(succ2Val.get(weakS));
						if (validity == null) {
							continue;
						}
						switch (validity) {
						case INVALID:
							return Validity.INVALID;
						case UNKNOWN:
							someResultWasUnknown = true;
							break;
						case NOT_CHECKED:
						case VALID:
							throw new AssertionError(CASE_MUST_NOT_OCCUR);
						default:
							throw new AssertionError(UNKNOWN_CASE);
						}
					}
				}
			}
		}
		{
			final Set<IPredicate> weakerThanPreHier = mPredicateUnifier.getCoverageRelation()
					.getCoveringPredicates(preHier);
			final Set<IPredicate> weakerThanPreLin = mPredicateUnifier.getCoverageRelation()
					.getCoveringPredicates(preLin);
			final Set<IPredicate> strongerThanSucc = mPredicateUnifier.getCoverageRelation().getCoveredPredicates(succ);

			final Iterable<IPredicate> predsHier = new IterableIntersection<>(preHier2preLin2succ.keySet(),
					weakerThanPreHier);
			for (final IPredicate weakPreHier : predsHier) {
				final NestedMap2<IPredicate, IPredicate, Validity> preLin2succ2Val = preHier2preLin2succ
						.get(weakPreHier);
				final Iterable<IPredicate> predsLin = new IterableIntersection<>(preLin2succ2Val.keySet(),
						weakerThanPreLin);
				for (final IPredicate weakPreLin : predsLin) {
					final Map<IPredicate, Validity> succ2Val = preLin2succ2Val.get(weakPreLin);
					final Iterable<IPredicate> succs = new IterableIntersection<>(succ2Val.keySet(), strongerThanSucc);
					for (final IPredicate weakS : succs) {
						final Validity validity = evaluteResultWeakerThanPreAndStrongerThanSucc(succ2Val.get(weakS));
						if (validity == null) {
							continue;
						}
						switch (validity) {
						case VALID:
							return Validity.VALID;
						case UNKNOWN:
							someResultWasUnknown = true;
							break;
						case NOT_CHECKED:
						case INVALID:
							throw new AssertionError(CASE_MUST_NOT_OCCUR);
						default:
							throw new AssertionError(UNKNOWN_CASE);
						}
					}
				}
			}
		}
		if (UNKNOWN_IF_SOME_EXTENDED_CHECK_IS_UNKNOWN && someResultWasUnknown) {
			// we pass this result as a warning that the corresponding check might be
			// expensive
			return Validity.UNKNOWN;
		}
		return null;
	}

	private Validity evaluteResultWeakerThanPreAndStrongerThanSucc(final Validity validity) {
		switch (validity) {
		case VALID:
			// pass result, if Hoare triple holds for weaker pre and for stronger succ,
			// it also does not hold for original pre/succ
			return validity;
		case UNKNOWN:
			// we pass this result as a warning that the corresponding check might be
			// expensive
			return validity;
		case INVALID:
			// information does not help
			return null;
		case NOT_CHECKED:
			return null;
		default:
			throw new AssertionError(UNKNOWN_CASE);
		}
	}

	private Validity evaluteResultStrongerThanPreAndWeakerThanSucc(final Validity validity) {
		switch (validity) {
		case VALID:
			// information does not help
			return null;
		case UNKNOWN:
			// we pass this result as a warning that the corresponding check might be
			// expensive
			return validity;
		case INVALID:
			// pass result, if Hoare triple does not hold for stronger pre and for weaker
			// succ,
			// it also does not hold for original pre/succ
			return validity;
		case NOT_CHECKED:
			return null;
		default:
			throw new AssertionError(UNKNOWN_CASE);
		}
	}
}
