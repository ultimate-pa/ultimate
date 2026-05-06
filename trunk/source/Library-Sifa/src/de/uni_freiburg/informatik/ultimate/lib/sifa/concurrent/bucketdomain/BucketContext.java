package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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

// TODO: merge into bucketdomain somehow if possible
public final class BucketContext implements IThreadLocalDomainContext {
	private static final String MAIN_THREAD = "ULTIMATE.start";

	@FunctionalInterface
	public interface BucketTransfer<T> {
		IPredicate apply(IPredicate sourceBucketState, T interference, IDomain domain);
	}

	private final SymbolicTools mTools;
	private final Map<String, Integer> mInitialBucketByThread;
	private String mCurrentThreadId;

	private BucketContext(final SymbolicTools tools, final Map<String, Integer> initialBucketByThread) {
		mTools = Objects.requireNonNull(tools);
		mInitialBucketByThread = Map.copyOf(initialBucketByThread);
	}

	@Override
	public void setCurrentThreadId(final String threadId) {
		mCurrentThreadId = threadId;
	}

	public Set<String> bucketedThreads() {
		return mInitialBucketByThread.keySet();
	}

	public boolean hasCurrentBuckets() {
		return mInitialBucketByThread.containsKey(mCurrentThreadId);
	}

	public IPredicate bottom() {
		return mTools.bottom();
	}

	public IPredicate toPredicate(final Map<Integer, IPredicate> buckets) {
		return BucketPredicate.of(mTools, buckets);
	}

	public <T> IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats, final Map<AbstractLocationPair, T> interferenceByAbstractLocationPair,
			final BucketTransfer<T> transfer) {
		final IDomain bucketDomain = domain instanceof final BucketDomain buckets ? buckets.baseDomain() : domain;
		Map<Integer, IPredicate> current = bucketsOf(state);
		Map<Integer, IPredicate> frontier = current;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			final Map<Integer, IPredicate> generated = new LinkedHashMap<>();
			for (final var entry : interferenceByAbstractLocationPair.entrySet()) {
				final IPredicate sourceState = frontier.get(entry.getKey().sourceAbstractLocation());
				if (sourceState != null) {
					merge(generated, entry.getKey().targetAbstractLocation(),
							transfer.apply(sourceState, entry.getValue(), bucketDomain), bucketDomain);
				}
			}
			if (generated.isEmpty() || isSubsetEq(generated, current, bucketDomain)) {
				return BucketPredicate.of(mTools, current);
			}
			final Map<Integer, IPredicate> expanded = join(current, generated, bucketDomain);
			final Map<Integer, IPredicate> next = iteration > wideningThreshold ? widen(current, expanded, bucketDomain)
					: expanded;
			if (iteration > wideningThreshold) {
				stats.increment(Key.INTERFERENCE_INNER_WIDENINGS);
			}
			if (isSubsetEq(next, current, bucketDomain)) {
				return BucketPredicate.of(mTools, current);
			}
			current = next;
			frontier = generated;
		}
	}

	public Map<Integer, IPredicate> bucketsOf(final IPredicate state) {
		if (state instanceof final BucketPredicate buckets) {
			return new LinkedHashMap<>(buckets.buckets());
		}
		return new LinkedHashMap<>(Map.of(mInitialBucketByThread.get(mCurrentThreadId), state));
	}

	private static void merge(final Map<Integer, IPredicate> buckets, final int bucket, final IPredicate state,
			final IDomain domain) {
		if (!SmtUtils.isFalseLiteral(state.getFormula())) {
			buckets.merge(bucket, state, domain::join);
		}
	}

	private boolean isSubsetEq(final Map<Integer, IPredicate> subset, final Map<Integer, IPredicate> superset,
			final IDomain domain) {
		for (final var entry : subset.entrySet()) {
			final IPredicate supersetBucket = superset.getOrDefault(entry.getKey(), mTools.bottom());
			if (!domain.isSubsetEq(entry.getValue(), supersetBucket).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	private static Map<Integer, IPredicate> join(final Map<Integer, IPredicate> left,
			final Map<Integer, IPredicate> right, final IDomain domain) {
		return combine(left, right, domain::join);
	}

	private static Map<Integer, IPredicate> widen(final Map<Integer, IPredicate> old,
			final Map<Integer, IPredicate> widenWith, final IDomain domain) {
		return combine(old, widenWith, domain::widen);
	}

	private static Map<Integer, IPredicate> combine(final Map<Integer, IPredicate> left,
			final Map<Integer, IPredicate> right, final BinaryOperator<IPredicate> operation) {
		final Map<Integer, IPredicate> result = new LinkedHashMap<>(left);
		right.forEach((bucket, state) -> result.merge(bucket, state, operation));
		return result;
	}

	public static BucketContext createIfUseful(final SymbolicTools tools, final List<String> threadIds,
			final Map<IcfgLocation, Integer> locationIds, final IIcfg<IcfgLocation> icfg) {
		final List<String> workers = threadIds.stream().filter(t -> !MAIN_THREAD.equals(t)).sorted().toList();
		if (workers.size() != 2 || locationIds.isEmpty() || !hasDirectMainTwoWorkerShape(workers, icfg)) {
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
		return entries.isEmpty() ? null : new BucketContext(tools, entries);
	}

	private static boolean hasDirectMainTwoWorkerShape(final List<String> workerThreads,
			final IIcfg<IcfgLocation> icfg) {
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
