package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BinaryOperator;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class BucketDomain implements IDomain, IThreadLocalDomainContext {
	private static final String MAIN_THREAD = "ULTIMATE.start";

	@FunctionalInterface
	public interface BucketTransfer<T> {
		IPredicate apply(IPredicate sourceBucketState, T interference, IDomain domain);
	}

	private final IDomain mUnderlyingDomain;
	private final SymbolicTools mTools;
	private final Map<String, Integer> mInitialBucketByThread;
	private String mCurrentThreadId;

	private BucketDomain(final IDomain base, final SymbolicTools tools,
			final Map<String, Integer> initialBucketByThread) {
		mUnderlyingDomain = base;
		mTools = tools;
		mInitialBucketByThread = Map.copyOf(initialBucketByThread);
	}

	public IDomain baseDomain() {
		return mUnderlyingDomain;
	}

	public Set<String> bucketedThreads() {
		return mInitialBucketByThread.keySet();
	}

	public boolean hasCurrentBuckets() {
		return mInitialBucketByThread.containsKey(mCurrentThreadId);
	}

	@Override
	public void setCurrentThreadId(final String threadId) {
		mCurrentThreadId = threadId;
		if (mUnderlyingDomain instanceof final IThreadLocalDomainContext threadLocal) {
			threadLocal.setCurrentThreadId(threadId);
		}
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		return combine(lhs, rhs, mUnderlyingDomain::join);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		return combine(old, widenWith, mUnderlyingDomain::widen);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		final Map<Integer, IPredicate> buckets = bucketsOrNull(pred);
		if (buckets == null) {
			return mUnderlyingDomain.isEqBottom(pred);
		}
		final Map<Integer, IPredicate> checked = new LinkedHashMap<>();
		boolean allBottom = true;
		boolean abstracted = false;
		for (final var entry : buckets.entrySet()) {
			final ResultForAlteredInputs result = mUnderlyingDomain.isEqBottom(entry.getValue());
			checked.put(entry.getKey(), result.getLhs());
			allBottom &= result.isTrueForAbstraction();
			abstracted |= result.wasAbstracted();
		}
		return new ResultForAlteredInputs(toPredicate(checked), bottom(), allBottom, abstracted);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		final Map<Integer, IPredicate> subsetBuckets = bucketsOrNull(subset);
		final Map<Integer, IPredicate> supersetBuckets = bucketsOrNull(superset);
		if (subsetBuckets == null || supersetBuckets == null) {
			return mUnderlyingDomain.isSubsetEq(subset, superset);
		}
		final Map<Integer, IPredicate> checkedSubset = new LinkedHashMap<>();
		final Map<Integer, IPredicate> checkedSuperset = new LinkedHashMap<>(supersetBuckets);
		boolean isSubset = true;
		boolean abstracted = false;
		for (final var entry : subsetBuckets.entrySet()) {
			final IPredicate bucketSuperset = supersetBuckets.getOrDefault(entry.getKey(), bottom());
			final ResultForAlteredInputs result = mUnderlyingDomain.isSubsetEq(entry.getValue(), bucketSuperset);
			checkedSubset.put(entry.getKey(), result.getLhs());
			checkedSuperset.put(entry.getKey(), result.getRhs());
			isSubset &= result.isTrueForAbstraction();
			abstracted |= result.wasAbstracted();
		}
		return new ResultForAlteredInputs(toPredicate(checkedSubset), toPredicate(checkedSuperset), isSubset,
				abstracted);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		final Map<Integer, IPredicate> buckets = bucketsOrNull(pred);
		if (buckets == null) {
			return mUnderlyingDomain.alpha(pred);
		}
		final Map<Integer, IPredicate> abstracted = new LinkedHashMap<>();
		buckets.forEach((bucket, state) -> abstracted.put(bucket, mUnderlyingDomain.alpha(state)));
		return toPredicate(abstracted);
	}

	private IPredicate bottom() {
		return mTools.bottom();
	}

	private IPredicate toPredicate(final Map<Integer, IPredicate> buckets) {
		return BucketPredicate.of(mTools, buckets);
	}

	private Map<Integer, IPredicate> bucketsOf(final IPredicate state) {
		if (state instanceof final BucketPredicate buckets) {
			return new LinkedHashMap<>(buckets.buckets());
		}
		return new LinkedHashMap<>(Map.of(mInitialBucketByThread.get(mCurrentThreadId), state));
	}

	private Map<Integer, IPredicate> bucketsOrNull(final IPredicate pred) {
		if (pred instanceof BucketPredicate || hasCurrentBuckets()) {
			return bucketsOf(pred);
		}
		return null;
	}

	public <T> IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats, final Map<AbstractLocationPair, T> interferenceByAbstractLocationPair,
			final BucketTransfer<T> transfer) {
		Map<Integer, IPredicate> current = bucketsOf(state);
		Map<Integer, IPredicate> frontier = current;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			final Map<Integer, IPredicate> generated = new LinkedHashMap<>();
			for (final var entry : interferenceByAbstractLocationPair.entrySet()) {
				final IPredicate sourceState = frontier.get(entry.getKey().sourceAbstractLocation());
				if (sourceState != null) {
					mapMerge(generated, entry.getKey().targetAbstractLocation(),
							transfer.apply(sourceState, entry.getValue(), mUnderlyingDomain), mUnderlyingDomain);
				}
			}
			if (generated.isEmpty() || mapIsSubsetEq(generated, current)) {
				return toPredicate(current);
			}
			final Map<Integer, IPredicate> expanded = mapCombine(current, generated, mUnderlyingDomain::join);
			final Map<Integer, IPredicate> next = iteration > wideningThreshold
					? mapCombine(current, expanded, mUnderlyingDomain::widen)
					: expanded;
			if (iteration > wideningThreshold) {
				stats.increment(Key.INTERFERENCE_INNER_WIDENINGS);
			}
			if (mapIsSubsetEq(next, current)) {
				return toPredicate(current);
			}
			current = next;
			frontier = generated;
		}
	}

	private static void mapMerge(final Map<Integer, IPredicate> buckets, final int bucket, final IPredicate state,
			final IDomain domain) {
		if (!SmtUtils.isFalseLiteral(state.getFormula())) {
			buckets.merge(bucket, state, domain::join);
		}
	}

	private boolean mapIsSubsetEq(final Map<Integer, IPredicate> subset, final Map<Integer, IPredicate> superset) {
		for (final var entry : subset.entrySet()) {
			final IPredicate supersetBucket = superset.getOrDefault(entry.getKey(), bottom());
			if (!mUnderlyingDomain.isSubsetEq(entry.getValue(), supersetBucket).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	private IPredicate combine(final IPredicate lhs, final IPredicate rhs, final BinaryOperator<IPredicate> operation) {
		final Map<Integer, IPredicate> left = bucketsOrNull(lhs);
		final Map<Integer, IPredicate> right = bucketsOrNull(rhs);
		if (left == null || right == null) {
			return operation.apply(lhs, rhs);
		}
		return toPredicate(mapCombine(left, right, operation));
	}

	private static Map<Integer, IPredicate> mapCombine(final Map<Integer, IPredicate> left,
			final Map<Integer, IPredicate> right, final BinaryOperator<IPredicate> operation) {
		final Map<Integer, IPredicate> result = new LinkedHashMap<>(left);
		right.forEach((bucket, state) -> result.merge(bucket, state, operation));
		return result;
	}

	public static BucketDomain createIfUseful(final IDomain base, final SymbolicTools tools,
			final List<String> threadIds, final Map<IcfgLocation, Integer> locationIds,
			final IIcfg<IcfgLocation> icfg) {
		final List<String> workers = threadIds.stream().filter(t -> !MAIN_THREAD.equals(t)).sorted().toList();
		if (workers.size() != 2 || locationIds.isEmpty() || !solvableByBuckets(workers, icfg)) {
			return null;
		}
		final Map<String, Integer> entries = new LinkedHashMap<>();
		for (final String thread : workers) {
			final Integer peerEntry = locationIds.get(
					icfg.getProcedureEntryNodes().get(thread.equals(workers.get(0)) ? workers.get(1) : workers.get(0)));
			if (peerEntry != null) {
				entries.put(thread, peerEntry);
			}
		}
		return entries.isEmpty() ? null : new BucketDomain(base, tools, entries);
	}

	private static boolean solvableByBuckets(final List<String> workerThreads, final IIcfg<IcfgLocation> icfg) {
		final Map<String, Set<String>> directForkTargets = new LinkedHashMap<>();
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			directForkTargets.computeIfAbsent(fork.getSource().getProcedure(), __ -> new LinkedHashSet<>())
					.add(fork.getNameOfForkedProcedure());
		}
		final Set<String> mainForkTargets = directForkTargets.getOrDefault(MAIN_THREAD, Set.of());
		return mainForkTargets.size() == workerThreads.size() && mainForkTargets.containsAll(workerThreads)
				&& workerThreads.stream().allMatch(t -> directForkTargets.getOrDefault(t, Set.of()).isEmpty());
	}
}
