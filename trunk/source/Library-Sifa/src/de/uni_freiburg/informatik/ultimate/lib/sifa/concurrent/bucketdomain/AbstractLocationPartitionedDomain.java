package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BinaryOperator;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

// IDomain wrapper that partitions abstract states by thread control location combinations.
// Combinations as in the Cartesian product |T1| x |T2| x ... x |Tn| over thread locations.
public final class AbstractLocationPartitionedDomain implements IDomain, IThreadLocalDomainContext {
	private final IDomain mUnderlyingDomain;
	private final SymbolicTools mTools;
	private final Map<String, String> mThreadIdByLocVarName;
	private String mCurrentThreadId;
	private Set<String> mRelevantThreadIds;

	private AbstractLocationPartitionedDomain(final IDomain underlying, final SymbolicTools tools,
			final Map<String, TermVariable> locVarsByThread) {
		mUnderlyingDomain = underlying;
		mTools = tools;
		final var threadByLocVarName = new LinkedHashMap<String, String>();
		for (final var entry : locVarsByThread.entrySet()) {
			threadByLocVarName.put(entry.getValue().getName(), entry.getKey());
		}
		mThreadIdByLocVarName = Map.copyOf(threadByLocVarName);
	}

	public static AbstractLocationPartitionedDomain create(final IDomain underlying, final SymbolicTools tools,
			final Map<String, TermVariable> locVarsByThread) {
		return new AbstractLocationPartitionedDomain(underlying, tools, locVarsByThread);
	}

	public IDomain underlyingDomain() {
		return mUnderlyingDomain;
	}

	@Override
	public void setCurrentThreadId(final String threadId) {
		mCurrentThreadId = threadId;
		if (mUnderlyingDomain instanceof final IThreadLocalDomainContext ctx) {
			ctx.setCurrentThreadId(threadId);
		}
	}

	public void setRelevantThreadIds(final Set<String> relevantThreadIds) {
		mRelevantThreadIds = relevantThreadIds == null ? null : Set.copyOf(relevantThreadIds);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		if (pred instanceof final AbstractLocationPartitionedPredicate bp) {
			return alphaEachPartition(bp.partitions());
		}
		return mUnderlyingDomain.alpha(pred);
	}

	private IPredicate alphaEachPartition(final Map<GlobalLocationState, IPredicate> partitions) {
		final Map<GlobalLocationState, IPredicate> abstracted = new LinkedHashMap<>();
		partitions.forEach((key, state) -> abstracted.put(key, mUnderlyingDomain.alpha(state)));
		return buildPredicateFromPartitionsMap(abstracted);
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		return combinePartitions(lhs, rhs, mUnderlyingDomain::join);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		return combinePartitions(old, widenWith, mUnderlyingDomain::widen);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		if (!(pred instanceof final AbstractLocationPartitionedPredicate bp)) {
			return mUnderlyingDomain.isEqBottom(pred);
		}
		final Map<GlobalLocationState, IPredicate> checkedPartitions = new LinkedHashMap<>();
		boolean allBottom = true;
		boolean anyAbstracted = false;
		for (final var entry : bp.partitions().entrySet()) {
			final ResultForAlteredInputs partitionResult = mUnderlyingDomain.isEqBottom(entry.getValue());
			checkedPartitions.put(entry.getKey(), partitionResult.getLhs());
			allBottom &= partitionResult.isTrueForAbstraction();
			anyAbstracted |= partitionResult.wasAbstracted();
		}
		return new ResultForAlteredInputs(buildPredicateFromPartitionsMap(checkedPartitions), mTools.bottom(), allBottom,
				anyAbstracted);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		final Map<GlobalLocationState, IPredicate> subParts = getPartitions(subset);
		final Map<GlobalLocationState, IPredicate> supParts = getPartitions(superset);
		// Avoid wrapping two plain predicates into the unknown partition.
		if (bothUnpartitioned(subParts, supParts)) {
			return mUnderlyingDomain.isSubsetEq(subParts.get(GlobalLocationState.UNKNOWN),
					supParts.get(GlobalLocationState.UNKNOWN));
		}
		final Map<GlobalLocationState, IPredicate> checkedSub = new LinkedHashMap<>();
		final Map<GlobalLocationState, IPredicate> checkedSup = new LinkedHashMap<>(supParts);
		boolean isSubset = true;
		boolean wasAbstracted = false;
		for (final var entry : subParts.entrySet()) {
			final IPredicate sup = supParts.getOrDefault(entry.getKey(), mTools.bottom());
			final ResultForAlteredInputs r = mUnderlyingDomain.isSubsetEq(entry.getValue(), sup);
			checkedSub.put(entry.getKey(), r.getLhs());
			checkedSup.put(entry.getKey(), r.getRhs());
			isSubset &= r.isTrueForAbstraction();
			wasAbstracted |= r.wasAbstracted();
		}
		return new ResultForAlteredInputs(buildPredicateFromPartitionsMap(checkedSub), buildPredicateFromPartitionsMap(checkedSup),
				isSubset, wasAbstracted);
	}

	public IPredicate buildPredicateFromPartitionsMap(final Map<GlobalLocationState, IPredicate> partitions) {
		final Map<GlobalLocationState, IPredicate> pruned = pruneToActiveThreads(partitions);
		final Map<GlobalLocationState, IPredicate> nonEmpty = filterBottom(pruned);
		if (nonEmpty.isEmpty()) {
			return mTools.bottom();
		}
		final List<Term> disjuncts = nonEmpty.values().stream().map(IPredicate::getFormula).toList();
		return AbstractLocationPartitionedPredicate.create(nonEmpty, mTools.orT(disjuncts));
	}

	private Map<GlobalLocationState, IPredicate> pruneToActiveThreads(final Map<GlobalLocationState, IPredicate> partitions) {
		final Map<GlobalLocationState, IPredicate> pruned = new LinkedHashMap<>();
		partitions.forEach((key, value) -> pruned.merge(restrictToActiveThreads(key), value, mUnderlyingDomain::join));
		return pruned;
	}

	private GlobalLocationState restrictToActiveThreads(final GlobalLocationState locState) {
		if (locState.locs().isEmpty()) {
			return GlobalLocationState.UNKNOWN;
		}
		final Map<String, Integer> pruned = new LinkedHashMap<>();
		for (final var entry : locState.locs().entrySet()) {
			if (isRelevantThread(mThreadIdByLocVarName.get(entry.getKey()))) {
				pruned.put(entry.getKey(), entry.getValue());
			}
		}
		return pruned.isEmpty() ? GlobalLocationState.UNKNOWN : new GlobalLocationState(pruned);
	}

	private boolean isRelevantThread(final String threadId) {
		if (threadId == null || threadId.equals(mCurrentThreadId)) {
			return false;
		}
		return mRelevantThreadIds == null || mRelevantThreadIds.contains(threadId);
	}

	private Map<GlobalLocationState, IPredicate> filterBottom(final Map<GlobalLocationState, IPredicate> partitions) {
		final Map<GlobalLocationState, IPredicate> result = new LinkedHashMap<>();
		partitions.forEach((key, value) -> {
			if (!SmtUtils.isFalseLiteral(value.getFormula())) {
				result.put(key, value);
			}
		});
		return result;
	}

	private IPredicate combinePartitions(final IPredicate lhs, final IPredicate rhs,
			final BinaryOperator<IPredicate> op) {
		final Map<GlobalLocationState, IPredicate> left = getPartitions(lhs);
		final Map<GlobalLocationState, IPredicate> right = getPartitions(rhs);
		if (bothUnpartitioned(left, right)) {
			return op.apply(left.get(GlobalLocationState.UNKNOWN), right.get(GlobalLocationState.UNKNOWN));
		}
		final Map<GlobalLocationState, IPredicate> result = new LinkedHashMap<>(left);
		right.forEach((k, v) -> result.merge(k, v, op));
		return buildPredicateFromPartitionsMap(result);
	}

	private static boolean bothUnpartitioned(final Map<GlobalLocationState, IPredicate> left,
			final Map<GlobalLocationState, IPredicate> right) {
		return left.size() <= 1 && right.size() <= 1 && left.containsKey(GlobalLocationState.UNKNOWN)
				&& right.containsKey(GlobalLocationState.UNKNOWN);
	}

	private Map<GlobalLocationState, IPredicate> getPartitions(final IPredicate pred) {
		if (pred instanceof final AbstractLocationPartitionedPredicate bp) {
			return bp.partitions();
		}
		return Map.of(GlobalLocationState.UNKNOWN, pred);
	}
}
