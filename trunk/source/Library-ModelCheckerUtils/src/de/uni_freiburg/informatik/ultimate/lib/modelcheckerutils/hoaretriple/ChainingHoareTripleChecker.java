/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript.ILockHolderWithVoluntaryLockRelease;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermClassifier;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator.Statistics;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

/**
 *
 * An {@link IHoareTripleChecker} that chains different {@link IHoareTripleChecker}s together. It queries the first
 * checker, and if the answer is different from {@link Validity#UNKNOWN} and {@link Validity#NOT_CHECKED}, it is
 * returned. If it is {@link Validity#UNKNOWN} or {@link Validity#NOT_CHECKED}, the next checker is queried, until no
 * checker remains.
 *
 * Benefits as opposed to other {@link IHoareTripleChecker}s include automatic statistics, protection, and review.
 *
 * TODO: Integrate Cache from {@link CachingHoareTripleChecker}
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ChainingHoareTripleChecker implements IHoareTripleChecker {

	private static final int LONG_CHECK_THRESHOLD_MS = 1000;
	private final List<IWrappedHoareTripleChecker> mHtcs;
	private final ILogger mLogger;
	private static final Predicate<IPredicate> SKIP_PRED = a -> false;
	private static final Predicate<IAction> SKIP_ACT = a -> false;

	private ChainingHoareTripleChecker(final ILogger logger) {
		this(logger, Collections.emptyList());
	}

	private ChainingHoareTripleChecker(final ILogger logger, final List<IWrappedHoareTripleChecker> list) {
		mLogger = logger;
		mHtcs = list;
		DataStructureUtils.filteredCast(mHtcs.stream(), ReviewedProtectedHtc.class)
				.forEach(a -> a.setLockRelease(this::releaseLock));
	}

	@Override
	public void releaseLock() {
		mHtcs.stream().forEach(IHoareTripleChecker::releaseLock);
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		for (final IWrappedHoareTripleChecker htc : mHtcs) {
			final Validity val = htc.checkInternal(pre, act, succ);
			htc.getUnderlying().reportLongChecks(pre, act, succ, val);
			if (val == Validity.INVALID || val == Validity.VALID) {
				return val;
			}
		}
		return Validity.UNKNOWN;
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		for (final IWrappedHoareTripleChecker htc : mHtcs) {
			final Validity val = htc.checkCall(pre, act, succ);
			htc.getUnderlying().reportLongChecks(pre, act, succ, val);
			if (val == Validity.INVALID || val == Validity.VALID) {
				return val;
			}
		}
		return Validity.UNKNOWN;
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		for (final IWrappedHoareTripleChecker htc : mHtcs) {
			final Validity val = htc.checkReturn(preLin, preHier, act, succ);
			htc.getUnderlying().reportLongChecks(preLin, preHier, act, succ, val);
			if (val == Validity.INVALID || val == Validity.VALID) {
				return val;
			}
		}
		return Validity.UNKNOWN;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		final StatisticsAggregator aggr = new StatisticsAggregator();
		for (final IWrappedHoareTripleChecker htc : mHtcs) {
			aggr.aggregateBenchmarkData(htc.getStatistics());
			final ProtectedHtc under = htc.getUnderlying();
			final String prefix = under.mHtc.getClass().getSimpleName();
			aggr.aggregateBenchmarkData(prefix, under.mStats);
		}
		return aggr;
	}

	@Override
	public String toString() {
		return mHtcs.stream().map(IHoareTripleChecker::toString).collect(Collectors.joining(", "));
	}

	/**
	 * Create a {@link ChainingHoareTripleChecker} with a single underlying {@link IHoareTripleChecker}.
	 *
	 * @param htc
	 *            The underlying {@link IHoareTripleChecker}.
	 * @return A new {@link ChainingHoareTripleChecker}.
	 */
	public static ChainingHoareTripleChecker with(final ILogger logger, final IHoareTripleChecker htc) {
		return new ChainingHoareTripleChecker(logger).andThen(htc);
	}

	public static ChainingHoareTripleChecker empty(final ILogger logger) {
		return new ChainingHoareTripleChecker(logger);
	}

	/**
	 * Add another {@link IHoareTripleChecker} to the {@link ChainingHoareTripleChecker}. The added
	 * {@link IHoareTripleChecker} will be queried when all the {@link IHoareTripleChecker}s before answered
	 * {@link Validity#UNKNOWN}.
	 *
	 * @param htc
	 *            The added {@link IHoareTripleChecker}.
	 * @return A new {@link ChainingHoareTripleChecker}.
	 */
	public ChainingHoareTripleChecker andThen(final IHoareTripleChecker htc) {
		if (htc instanceof ChainingHoareTripleChecker) {
			final ChainingHoareTripleChecker chain = (ChainingHoareTripleChecker) htc;
			ChainingHoareTripleChecker rtr = this;
			for (final IWrappedHoareTripleChecker wHtc : chain.mHtcs) {
				rtr = rtr.add(wHtc.copy());
			}
			return rtr;
		}
		return add(new ProtectedHtc(mLogger, htc, SKIP_ACT, SKIP_PRED));
	}

	/**
	 * Protect the last added {@link IHoareTripleChecker} from {@link IPredicate}s with a {@link Predicate} pred. All
	 * {@link IPredicate}s of a Hoare triple are tested by pred, and if pred tests true, no Hoare triple check is
	 * performed and {@link Validity#NOT_CHECKED} is returned immediately. If the last {@link IHoareTripleChecker} is
	 * already protected by a {@link Predicate}, it will now be protected by a disjunction of {@link Predicate}s.
	 *
	 * @param pred
	 *            A predicate that tests predicates of Hoare triples. If it returns true, no Hoare triple check is
	 *            performed.
	 * @return A new {@link ChainingHoareTripleChecker} where the last {@link IHoareTripleChecker} is protected.
	 */
	public ChainingHoareTripleChecker predicatesProtectedBy(final Predicate<IPredicate> pred) {
		return replaceLast(createFromLastProtected(last -> new ProtectedHtc(last.mLogger, last.mHtc,
				last.mPredActionProtection, last.mPredPredicateProtection.or(pred))));
	}

	/**
	 * Protect the last added {@link IHoareTripleChecker} from {@link IAction}s with a {@link Predicate} pred. The
	 * {@link IAction} of a Hoare triple is tested by pred, and if pred tests true, no Hoare triple check is performed
	 * and {@link Validity#NOT_CHECKED} is returned immediately. If the last {@link IHoareTripleChecker} is already
	 * protected by a {@link Predicate}, it will now be protected by a disjunction of {@link Predicate}s.
	 *
	 * @param pred
	 *            A predicate that tests actions of Hoare triples. If it returns true, no Hoare triple check is
	 *            performed.
	 * @return A new {@link ChainingHoareTripleChecker} where the last {@link IHoareTripleChecker} is protected.
	 */
	public ChainingHoareTripleChecker actionsProtectedBy(final Predicate<IAction> pred) {
		return replaceLast(createFromLastProtected(last -> new ProtectedHtc(last.mLogger, last.mHtc,
				last.mPredActionProtection.or(pred), last.mPredPredicateProtection)));
	}

	/**
	 * Add a {@link IHoareTripleChecker} that reviews the results of the last {@link IHoareTripleChecker} when
	 * assertions are enabled.
	 *
	 * @param reviewHtc
	 *            The {@link IHoareTripleChecker} that performs the reviewing.
	 * @return A new {@link ChainingHoareTripleChecker} where the last {@link IHoareTripleChecker} is reviewed.
	 */
	public ChainingHoareTripleChecker reviewWith(final IHoareTripleChecker reviewHtc) {
		if (VMUtils.areAssertionsEnabled()) {
			return replaceLast(createFromLastReview(reviewHtc));
		}
		return this;
	}

	private ChainingHoareTripleChecker replaceLast(final IWrappedHoareTripleChecker replacement) {
		final List<IWrappedHoareTripleChecker> list = new ArrayList<>(mHtcs.size());
		list.addAll(mHtcs);
		list.set(list.size() - 1, replacement);
		return new ChainingHoareTripleChecker(mLogger, list);
	}

	private ChainingHoareTripleChecker add(final IWrappedHoareTripleChecker add) {
		final List<IWrappedHoareTripleChecker> list = new ArrayList<>(mHtcs.size() + 1);
		list.addAll(mHtcs);
		list.add(add);
		return new ChainingHoareTripleChecker(mLogger, list);
	}

	private IWrappedHoareTripleChecker getLast() {
		return mHtcs.get(mHtcs.size() - 1);
	}

	private IWrappedHoareTripleChecker createFromLastReview(final IHoareTripleChecker reviewHtc) {
		final ProtectedHtc pHtc = getLast().getUnderlying();
		return new ReviewedProtectedHtc(reviewHtc,
				new ProtectedHtc(pHtc.mLogger, pHtc.mHtc, pHtc.mPredActionProtection, pHtc.mPredPredicateProtection));
	}

	private IWrappedHoareTripleChecker createFromLastProtected(final Function<ProtectedHtc, ProtectedHtc> replace) {
		final IWrappedHoareTripleChecker last = getLast();
		return last.replaceUnderlying(replace.apply(last.getUnderlying()));
	}

	private interface IWrappedHoareTripleChecker extends IHoareTripleChecker {
		ProtectedHtc getUnderlying();

		IWrappedHoareTripleChecker replaceUnderlying(final ProtectedHtc underlying);

		/**
		 * Create a copy that keeps everything except statistics.
		 */
		IWrappedHoareTripleChecker copy();
	}

	private static class ReviewedProtectedHtc implements IWrappedHoareTripleChecker {

		private final IHoareTripleChecker mReviewHtc;
		private final ProtectedHtc mHtc;
		private ILockHolderWithVoluntaryLockRelease mFunReleaseLocks;

		/**
		 *
		 * @param reviewHtc
		 *            The {@link IHoareTripleChecker} used for reviewing.
		 * @param htc
		 *            The actual {@link IHoareTripleChecker}
		 * @param funReleaseLocks
		 *            A function that releases {@link ManagedScript} locks before reviewing.
		 */
		public ReviewedProtectedHtc(final IHoareTripleChecker reviewHtc, final ProtectedHtc htc) {
			mReviewHtc = Objects.requireNonNull(reviewHtc);
			mHtc = Objects.requireNonNull(htc);
		}

		private void setLockRelease(final ILockHolderWithVoluntaryLockRelease funReleaseLocks) {
			mFunReleaseLocks = funReleaseLocks;
		}

		@Override
		public void releaseLock() {
			mHtc.releaseLock();
			mReviewHtc.releaseLock();
		}

		@Override
		public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
			final Validity val = mHtc.checkInternal(pre, act, succ);
			if (val == Validity.NOT_CHECKED || val == Validity.UNKNOWN) {
				return val;
			}
			assert reviewInductiveInternal(pre, act, succ, val);
			return val;
		}

		@Override
		public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
			final Validity val = mHtc.checkCall(pre, act, succ);
			if (val == Validity.NOT_CHECKED || val == Validity.UNKNOWN) {
				return val;
			}
			assert reviewInductiveCall(pre, act, succ, val);
			return val;
		}

		@Override
		public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
				final IPredicate succ) {
			final Validity val = mHtc.checkReturn(preLin, preHier, act, succ);
			if (val == Validity.NOT_CHECKED || val == Validity.UNKNOWN) {
				return val;
			}
			assert reviewInductiveReturn(preLin, preHier, act, succ, val);
			return val;
		}

		private boolean reviewInductiveInternal(final IPredicate state, final IInternalAction act,
				final IPredicate succ, final Validity result) {
			mFunReleaseLocks.releaseLock();
			final Validity reviewResult = mReviewHtc.checkInternal(state, act, succ);
			if (reviewResult(result, reviewResult)) {
				mReviewHtc.releaseLock();
				return true;
			}
			throw createAssertionError(result, reviewResult);
		}

		private boolean reviewInductiveCall(final IPredicate state, final ICallAction act, final IPredicate succ,
				final Validity result) {
			mFunReleaseLocks.releaseLock();
			final Validity reviewResult = mReviewHtc.checkCall(state, act, succ);
			if (reviewResult(result, reviewResult)) {
				mReviewHtc.releaseLock();
				return true;
			}
			throw createAssertionError(result, reviewResult);

		}

		private boolean reviewInductiveReturn(final IPredicate state, final IPredicate hier, final IReturnAction act,
				final IPredicate succ, final Validity result) {
			mFunReleaseLocks.releaseLock();
			final Validity reviewResult = mReviewHtc.checkReturn(state, hier, act, succ);
			if (reviewResult(result, reviewResult)) {
				mReviewHtc.releaseLock();
				return true;
			}
			throw createAssertionError(result, reviewResult);
		}

		/**
		 * Return true if results are compatible or one is UNKNOWN
		 */
		private static boolean reviewResult(final Validity result, final Validity reviewResult) {
			switch (result) {
			case VALID:
				return reviewResult == Validity.VALID || reviewResult == Validity.UNKNOWN;
			case INVALID:
				return reviewResult == Validity.INVALID || reviewResult == Validity.UNKNOWN;
			case UNKNOWN:
			case NOT_CHECKED:
				return true;
			default:
				throw new UnsupportedOperationException("Unknown validity: " + result);
			}
		}

		private AssertionError createAssertionError(final Validity result, final Validity reviewResult) {
			return new AssertionError(String.format(
					"HoareTripleChecker results differ between %s (result: %s) and %s (result: %s)",
					mHtc.mHtc.getClass().getSimpleName(), result, mReviewHtc.getClass().getSimpleName(), reviewResult));
		}

		@Override
		public IStatisticsDataProvider getStatistics() {
			return mHtc.getStatistics();
		}

		@Override
		public String toString() {
			return mHtc.toString();
		}

		@Override
		public ProtectedHtc getUnderlying() {
			return mHtc;
		}

		@Override
		public IWrappedHoareTripleChecker replaceUnderlying(final ProtectedHtc underlying) {
			return new ReviewedProtectedHtc(mReviewHtc, underlying);
		}

		@Override
		public IWrappedHoareTripleChecker copy() {
			return new ReviewedProtectedHtc(mReviewHtc, new ProtectedHtc(mHtc.getUnderlying()));
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static class ProtectedHtc implements IWrappedHoareTripleChecker {
		private final IHoareTripleChecker mHtc;
		private final Predicate<IPredicate> mPredPredicateProtection;
		private final Predicate<IAction> mPredActionProtection;
		private final ValidityInCaReCounter mStats;
		private final ILogger mLogger;

		public ProtectedHtc(final ILogger logger, final IHoareTripleChecker htc,
				final Predicate<IAction> predActionProtection, final Predicate<IPredicate> predPredicateProtection) {
			mLogger = Objects.requireNonNull(logger);
			mHtc = Objects.requireNonNull(htc);
			mPredPredicateProtection = Objects.requireNonNull(predPredicateProtection);
			mPredActionProtection = Objects.requireNonNull(predActionProtection);
			mStats = new ValidityInCaReCounter();
		}

		public ProtectedHtc(final ProtectedHtc old) {
			this(old.mLogger, old.mHtc, old.mPredActionProtection, old.mPredPredicateProtection);
		}

		@Override
		public void releaseLock() {
			mHtc.releaseLock();
		}

		@Override
		public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
			final Validity val;
			mStats.start();
			if (mPredPredicateProtection.test(pre) || mPredPredicateProtection.test(succ)
					|| mPredActionProtection.test(act)) {
				val = Validity.NOT_CHECKED;
			} else {
				val = mHtc.checkInternal(pre, act, succ);
			}
			mStats.stop();
			mStats.inc(val, act);
			return val;
		}

		@Override
		public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
			final Validity val;
			mStats.start();
			if (mPredPredicateProtection.test(pre) || mPredPredicateProtection.test(succ)
					|| mPredActionProtection.test(act)) {
				val = Validity.NOT_CHECKED;
			} else {
				val = mHtc.checkCall(pre, act, succ);
			}
			mStats.stop();
			mStats.inc(val, act);
			return val;
		}

		@Override
		public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
				final IPredicate succ) {
			final Validity val;
			mStats.start();
			if (mPredPredicateProtection.test(preLin) || mPredPredicateProtection.test(preHier)
					|| mPredPredicateProtection.test(succ) || mPredActionProtection.test(act)) {
				val = Validity.NOT_CHECKED;
			} else {
				val = mHtc.checkReturn(preLin, preHier, act, succ);
			}
			mStats.stop();
			mStats.inc(val, act);
			return val;
		}

		@Override
		public IStatisticsDataProvider getStatistics() {
			return mHtc.getStatistics();
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append(mHtc.getClass().getSimpleName());
			sb.append(" [");
			sb.append(mStats);
			sb.append("]");
			return sb.toString();
		}

		@Override
		public ProtectedHtc getUnderlying() {
			return this;
		}

		@Override
		public IWrappedHoareTripleChecker replaceUnderlying(final ProtectedHtc underlying) {
			return underlying;
		}

		public void reportLongChecks(final IPredicate pre, final IAction act, final IPredicate succ,
				final Validity result) {
			reportLongChecks(pre, null, act, succ, result);
		}

		public void reportLongChecks(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ, final Validity result) {
			final long delta = mStats.mTime.lastDelta(TimeUnit.MILLISECONDS);
			if (delta > LONG_CHECK_THRESHOLD_MS) {
				final TermClassifier tc = new TermClassifier();
				tc.checkTerm(act.getTransformula().getFormula());
				tc.checkTerm(preLin.getFormula());
				tc.checkTerm(succ.getFormula());
				if (preHier != null) {
					tc.checkTerm(preHier.getFormula());
				}
				mLogger.warn(
						"%s took %s for a HTC check with result %s. Formula has sorts %s, hasArrays=%s, hasNonlinArith=%s, quantifiers %s",
						mHtc.getClass().getSimpleName(), CoreUtil.humanReadableTime(delta, TimeUnit.MILLISECONDS, 2),
						result, tc.getOccuringSortNames(), tc.hasArrays(), tc.hasNonlinearArithmetic(),
						tc.getOccuringQuantifiers());
			}
		}

		@Override
		public IWrappedHoareTripleChecker copy() {
			return new ProtectedHtc(this);
		}

	}

	private static final class ValidityInCaReCounter extends AbstractStatisticsDataProvider {

		@Reflected(prettyName = "Valid")
		@Statistics(type = KeyType.IN_CA_RE_COUNTER)
		private final InCaReCounter mValid = new InCaReCounter();

		@Reflected(prettyName = "Invalid")
		@Statistics(type = KeyType.IN_CA_RE_COUNTER)
		private final InCaReCounter mInvalid = new InCaReCounter();

		@Reflected(prettyName = "Unknown")
		@Statistics(type = KeyType.IN_CA_RE_COUNTER)
		private final InCaReCounter mUnknown = new InCaReCounter();

		@Reflected(prettyName = "Unchecked")
		@Statistics(type = KeyType.IN_CA_RE_COUNTER)
		private final InCaReCounter mUnchecked = new InCaReCounter();

		@Reflected(prettyName = "Time")
		@Statistics(type = KeyType.TT_TIMER)
		private final TimeTracker mTime = new TimeTracker();

		@Reflected(excluded = true)
		private static final Lazy<List<Field>> FIELDS =
				new Lazy<>(() -> ReflectionUtil.instanceFields(ValidityInCaReCounter.class).stream()
						.filter(f -> f.getAnnotation(Statistics.class) != null).collect(Collectors.toList()));

		public ValidityInCaReCounter() {
			for (final Field f : FIELDS.get()) {
				final Statistics annot = f.getAnnotation(Statistics.class);
				declare(ReflectionUtil.fieldPrettyName(f), () -> annot.type().convert(ReflectionUtil.access(this, f)),
						annot.type());
			}
		}

		public void start() {
			mTime.start();
		}

		public void stop() {
			mTime.stop();
		}

		public void inc(final Validity val, final IAction action) {
			switch (val) {
			case INVALID:
				inc(action, mInvalid);
				break;
			case NOT_CHECKED:
				inc(action, mUnchecked);
				break;
			case UNKNOWN:
				inc(action, mUnknown);
				break;
			case VALID:
				inc(action, mValid);
				break;
			default:
				throw new UnsupportedOperationException("Unknown validity " + val);
			}
		}

		private void inc(final IAction act, final InCaReCounter cnt) {
			if (act instanceof IInternalAction) {
				cnt.incIn();
			} else if (act instanceof ICallAction) {
				cnt.incCa();
			} else if (act instanceof IReturnAction) {
				cnt.incRe();
			} else {
				throw new UnsupportedOperationException("Unknown action " + act.getClass());
			}
		}

		@Override
		public String toString() {
			return getBenchmarkType().prettyprintBenchmarkData(this);
		}

	}

}
