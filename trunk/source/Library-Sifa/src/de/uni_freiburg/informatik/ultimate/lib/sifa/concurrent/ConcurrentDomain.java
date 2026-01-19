package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Wrapper domain for thread-modular analysis based on SIFA.
 */
public class ConcurrentDomain implements IDomain {

	private final IDomain mUnderlyingDomain;
	private final String mCurrentThread;
	private final Map<String, Set<IPredicate>> mInterferences;

	public ConcurrentDomain(final IDomain underlyingDomain, final String currentThread) {
		this(underlyingDomain, currentThread, Collections.emptyMap());
	}

	public ConcurrentDomain(final IDomain underlyingDomain, final String currentThread,
			final Map<String, Set<IPredicate>> interferences) {
		mUnderlyingDomain = underlyingDomain;
		mCurrentThread = currentThread;
		mInterferences = interferences;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		return mUnderlyingDomain.join(lhs, rhs);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		return mUnderlyingDomain.widen(old, widenWith);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		return mUnderlyingDomain.isEqBottom(pred);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		return mUnderlyingDomain.isSubsetEq(subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		// TODO:
		// Interferences
		return mUnderlyingDomain.alpha(pred);
	}

	public IDomain getUnderlyingDomain() {
		return mUnderlyingDomain;
	}

	public String getCurrentThread() {
		return mCurrentThread;
	}

	public Map<String, Set<IPredicate>> getInterferences() {
		return mInterferences;
	}

	public ConcurrentDomain forThread(final String newCurrentThread) {
		return new ConcurrentDomain(mUnderlyingDomain, newCurrentThread, mInterferences);
	}

	public ConcurrentDomain withInterferences(final Map<String, Set<IPredicate>> newInterferences) {
		return new ConcurrentDomain(mUnderlyingDomain, mCurrentThread, newInterferences);
	}
}
