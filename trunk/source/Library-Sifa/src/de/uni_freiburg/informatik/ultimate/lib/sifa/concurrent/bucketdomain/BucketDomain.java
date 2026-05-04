package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.BinaryOperator;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public final class BucketDomain implements IDomain, IThreadLocalDomainContext {
	private final IDomain mUnderlyingDomain;
	private final BucketContext mContext;

	public BucketDomain(final IDomain base, final BucketContext context) {
		mUnderlyingDomain = base;
		mContext = context;
	}

	public IDomain baseDomain() {
		return mUnderlyingDomain;
	}

	@Override
	public void setCurrentThreadId(final String threadId) {
		mContext.setCurrentThreadId(threadId);
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
		return new ResultForAlteredInputs(mContext.toPredicate(checked), mContext.bottom(), allBottom, abstracted);
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
			final IPredicate bucketSuperset = supersetBuckets.getOrDefault(entry.getKey(), mContext.bottom());
			final ResultForAlteredInputs result = mUnderlyingDomain.isSubsetEq(entry.getValue(), bucketSuperset);
			checkedSubset.put(entry.getKey(), result.getLhs());
			checkedSuperset.put(entry.getKey(), result.getRhs());
			isSubset &= result.isTrueForAbstraction();
			abstracted |= result.wasAbstracted();
		}
		return new ResultForAlteredInputs(mContext.toPredicate(checkedSubset), mContext.toPredicate(checkedSuperset),
				isSubset, abstracted);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		final Map<Integer, IPredicate> buckets = bucketsOrNull(pred);
		if (buckets == null) {
			return mUnderlyingDomain.alpha(pred);
		}
		final Map<Integer, IPredicate> abstracted = new LinkedHashMap<>();
		buckets.forEach((bucket, state) -> abstracted.put(bucket, mUnderlyingDomain.alpha(state)));
		return mContext.toPredicate(abstracted);
	}

	private IPredicate combine(final IPredicate lhs, final IPredicate rhs,
			final BinaryOperator<IPredicate> operation) {
		final Map<Integer, IPredicate> left = bucketsOrNull(lhs);
		final Map<Integer, IPredicate> right = bucketsOrNull(rhs);
		if (left == null || right == null) {
			return operation.apply(lhs, rhs);
		}
		final Map<Integer, IPredicate> result = new LinkedHashMap<>(left);
		right.forEach((bucket, state) -> result.merge(bucket, state, operation));
		return mContext.toPredicate(result);
	}

	private Map<Integer, IPredicate> bucketsOrNull(final IPredicate pred) {
		if (pred instanceof BucketPredicate || mContext.hasCurrentBuckets()) {
			return mContext.bucketsOf(pred);
		}
		return null;
	}
}
