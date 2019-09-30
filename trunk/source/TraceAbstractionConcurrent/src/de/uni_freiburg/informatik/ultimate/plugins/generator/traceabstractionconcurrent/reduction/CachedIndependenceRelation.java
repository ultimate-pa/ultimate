package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * An independence relation that caches the result of an underlying relation.
 * To be used with computation-intensive independence relations.
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class CachedIndependenceRelation<STATE, LETTER> implements IIndependenceRelation<STATE, LETTER> {
	
	private final IIndependenceRelation<STATE, LETTER> mUnderlying;
	private final Map<STATE, HashRelation<LETTER, LETTER>> mPositiveCache = new HashMap<>();
	private final Map<STATE, HashRelation<LETTER, LETTER>> mNegativeCache = new HashMap<>();
	
	public CachedIndependenceRelation(final IIndependenceRelation<STATE, LETTER> underlying) {
		mUnderlying = underlying;
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mUnderlying.isConditional();
	}

	@Override
	public boolean contains(final STATE state, final LETTER a, final LETTER b) {
		STATE stateKey = state;
		if (!isConditional()) {
			stateKey = null;
		}
		
		HashRelation<LETTER, LETTER> positive = mPositiveCache.get(stateKey);
		if (positive == null) {
			positive = new HashRelation<>();
		}

		HashRelation<LETTER, LETTER> negative = mNegativeCache.get(stateKey);
		if (negative == null) {
			negative = new HashRelation<>();
		}
		
		if (positive.containsPair(a, b) || (isSymmetric() && positive.containsPair(b, a))) {
			return true;
		} else if (negative.containsPair(a, b) || (isSymmetric() && positive.containsPair(b, a))) {
			return false;
		}

		final boolean result = mUnderlying.contains(state, a, b);
		if (result) {
			positive.addPair(a, b);
			mPositiveCache.put(stateKey, positive);
		} else {
			negative.addPair(a, b);
			mNegativeCache.put(stateKey, negative);
		}
		
		return result;
	}
}
