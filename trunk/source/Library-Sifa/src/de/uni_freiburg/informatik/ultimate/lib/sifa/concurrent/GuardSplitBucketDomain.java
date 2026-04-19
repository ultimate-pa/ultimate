package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Compatibility shim for callers still using the historic package.
 */
public final class GuardSplitBucketDomain implements IDomain, IThreadLocalDomainContext {

	public static record GuardBucketPolicy(String peerThreadId, TermVariable bucketVariable,
			Map<Integer, Integer> rawValueToBucket, Map<Integer, Set<Integer>> bucketToRawValues) {

		de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.GuardSplitBucketDomain.GuardBucketPolicy
				toInternalPolicy() {
			return new de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.GuardSplitBucketDomain.GuardBucketPolicy(
					peerThreadId, bucketVariable, rawValueToBucket, bucketToRawValues);
		}
	}

	private final de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.GuardSplitBucketDomain mDelegate;

	public GuardSplitBucketDomain(final SymbolicTools tools, final IDomain innerDomain,
			final Map<String, GuardBucketPolicy> policiesByThread) {
		mDelegate = new de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.GuardSplitBucketDomain(
				tools, innerDomain, convertPolicies(policiesByThread));
	}

	@Override
	public void setCurrentThreadId(final String threadId) {
		mDelegate.setCurrentThreadId(threadId);
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		return mDelegate.join(lhs, rhs);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		return mDelegate.widen(old, widenWith);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		return mDelegate.isEqBottom(pred);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		return mDelegate.isSubsetEq(subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		return mDelegate.alpha(pred);
	}

	private static Map<String, de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.GuardSplitBucketDomain.GuardBucketPolicy>
			convertPolicies(final Map<String, GuardBucketPolicy> policiesByThread) {
		final Map<String, de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.GuardSplitBucketDomain.GuardBucketPolicy>
				converted = new java.util.LinkedHashMap<>();
		for (final var entry : policiesByThread.entrySet()) {
			converted.put(entry.getKey(), entry.getValue().toInternalPolicy());
		}
		return converted;
	}
}
