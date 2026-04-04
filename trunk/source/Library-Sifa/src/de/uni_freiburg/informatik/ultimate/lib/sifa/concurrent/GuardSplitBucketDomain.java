package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class GuardSplitBucketDomain implements IDomain, IThreadLocalDomainContext {

	public static record GuardBucketPolicy(String peerThreadId, TermVariable bucketVariable,
			Map<Integer, Integer> rawValueToBucket, Map<Integer, Set<Integer>> bucketToRawValues) {

		public GuardBucketPolicy {
			Objects.requireNonNull(peerThreadId);
			Objects.requireNonNull(bucketVariable);
			Objects.requireNonNull(rawValueToBucket);
			Objects.requireNonNull(bucketToRawValues);
			rawValueToBucket = Map.copyOf(rawValueToBucket);
			final Map<Integer, Set<Integer>> immutableBuckets = new LinkedHashMap<>();
			for (final var entry : bucketToRawValues.entrySet()) {
				immutableBuckets.put(entry.getKey(), Set.copyOf(entry.getValue()));
			}
			bucketToRawValues = Map.copyOf(immutableBuckets);
		}

		public Integer bucketForRawValue(final int rawValue) {
			return rawValueToBucket.get(rawValue);
		}

		public Set<Integer> rawValuesForBucket(final int bucket) {
			return bucketToRawValues.getOrDefault(bucket, Set.of());
		}
	}

	private static record BucketKey(int locationBucket) {
	}

	private final SymbolicTools mTools;
	private final IDomain mInnerDomain;
	private final Map<String, GuardBucketPolicy> mPoliciesByThread;
	private String mCurrentThreadId;

	public GuardSplitBucketDomain(final SymbolicTools tools, final IDomain innerDomain,
			final Map<String, GuardBucketPolicy> policiesByThread) {
		mTools = Objects.requireNonNull(tools);
		mInnerDomain = Objects.requireNonNull(innerDomain);
		mPoliciesByThread = Map.copyOf(Objects.requireNonNull(policiesByThread));
	}

	@Override
	public void setCurrentThreadId(final String threadId) {
		mCurrentThreadId = threadId;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		final GuardBucketPolicy policy = currentPolicyOrNull();
		if (policy == null) {
			return mInnerDomain.join(lhs, rhs);
		}
		final Map<BucketKey, IPredicate> lhsBuckets = splitIntoBuckets(lhs, policy);
		final Map<BucketKey, IPredicate> rhsBuckets = splitIntoBuckets(rhs, policy);
		if (lhsBuckets == null || rhsBuckets == null) {
			return mInnerDomain.join(lhs, rhs);
		}
		final Map<BucketKey, IPredicate> joinedBuckets = new LinkedHashMap<>();
		final Set<BucketKey> allBuckets = new LinkedHashSet<>(lhsBuckets.keySet());
		allBuckets.addAll(rhsBuckets.keySet());
		for (final BucketKey bucket : allBuckets) {
			final IPredicate leftBucket = lhsBuckets.get(bucket);
			final IPredicate rightBucket = rhsBuckets.get(bucket);
			if (leftBucket == null) {
				joinedBuckets.put(bucket, rightBucket);
			} else if (rightBucket == null) {
				joinedBuckets.put(bucket, leftBucket);
			} else {
				joinedBuckets.put(bucket, mInnerDomain.join(leftBucket, rightBucket));
			}
		}
		return composeBuckets(joinedBuckets, policy);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		final GuardBucketPolicy policy = currentPolicyOrNull();
		if (policy == null) {
			return mInnerDomain.widen(old, widenWith);
		}
		final Map<BucketKey, IPredicate> oldBuckets = splitIntoBuckets(old, policy);
		final Map<BucketKey, IPredicate> widenBuckets = splitIntoBuckets(widenWith, policy);
		if (oldBuckets == null || widenBuckets == null) {
			return mInnerDomain.widen(old, widenWith);
		}
		final Map<BucketKey, IPredicate> widened = new LinkedHashMap<>();
		final Set<BucketKey> allBuckets = new LinkedHashSet<>(oldBuckets.keySet());
		allBuckets.addAll(widenBuckets.keySet());
		for (final BucketKey bucket : allBuckets) {
			final IPredicate oldBucket = oldBuckets.get(bucket);
			final IPredicate widenBucket = widenBuckets.get(bucket);
			if (oldBucket == null) {
				widened.put(bucket, widenBucket);
			} else if (widenBucket == null) {
				widened.put(bucket, oldBucket);
			} else {
				widened.put(bucket, mInnerDomain.widen(oldBucket, widenBucket));
			}
		}
		return composeBuckets(widened, policy);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		final GuardBucketPolicy policy = currentPolicyOrNull();
		if (policy == null) {
			return mInnerDomain.isEqBottom(pred);
		}
		final Map<BucketKey, IPredicate> buckets = splitIntoBuckets(pred, policy);
		if (buckets == null) {
			return mInnerDomain.isEqBottom(pred);
		}
		boolean abstracted = false;
		for (final IPredicate bucketPred : buckets.values()) {
			final ResultForAlteredInputs result = mInnerDomain.isEqBottom(bucketPred);
			abstracted |= result.wasAbstracted();
			if (!result.isTrueForAbstraction()) {
				return new ResultForAlteredInputs(pred, null, false, abstracted);
			}
		}
		return new ResultForAlteredInputs(pred, null, true, abstracted);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		final GuardBucketPolicy policy = currentPolicyOrNull();
		if (policy == null) {
			return mInnerDomain.isSubsetEq(subset, superset);
		}
		final Map<BucketKey, IPredicate> subsetBuckets = splitIntoBuckets(subset, policy);
		final Map<BucketKey, IPredicate> supersetBuckets = splitIntoBuckets(superset, policy);
		if (subsetBuckets == null || supersetBuckets == null) {
			return mInnerDomain.isSubsetEq(subset, superset);
		}
		boolean abstracted = false;
		for (final var entry : subsetBuckets.entrySet()) {
			final IPredicate supersetBucket = supersetBuckets.getOrDefault(entry.getKey(), mTools.bottom());
			final ResultForAlteredInputs result = mInnerDomain.isSubsetEq(entry.getValue(), supersetBucket);
			abstracted |= result.wasAbstracted();
			if (!result.isTrueForAbstraction()) {
				return new ResultForAlteredInputs(subset, superset, false, abstracted);
			}
		}
		return new ResultForAlteredInputs(subset, superset, true, abstracted);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		final GuardBucketPolicy policy = currentPolicyOrNull();
		if (policy == null) {
			return mInnerDomain.alpha(pred);
		}
		final Map<BucketKey, IPredicate> buckets = splitIntoBuckets(pred, policy);
		if (buckets == null) {
			return mInnerDomain.alpha(pred);
		}
		final Map<BucketKey, IPredicate> abstractedBuckets = new LinkedHashMap<>();
		for (final var entry : buckets.entrySet()) {
			abstractedBuckets.put(entry.getKey(), mInnerDomain.alpha(entry.getValue()));
		}
		return composeBuckets(abstractedBuckets, policy);
	}

	private GuardBucketPolicy currentPolicyOrNull() {
		if (mCurrentThreadId == null) {
			return null;
		}
		return mPoliciesByThread.get(mCurrentThreadId);
	}

	private Map<BucketKey, IPredicate> splitIntoBuckets(final IPredicate pred, final GuardBucketPolicy policy) {
		final Map<BucketKey, IPredicate> directSplit = trySplitIntoBuckets(SmtUtils.getDisjuncts(pred.getFormula()), policy);
		if (directSplit != null) {
			return directSplit;
		}
		return trySplitIntoBuckets(mTools.dnfDisjuncts(pred), policy);
	}

	private Map<BucketKey, IPredicate> trySplitIntoBuckets(final Term[] disjuncts, final GuardBucketPolicy policy) {
		final Map<BucketKey, List<Term>> bucketTerms = new LinkedHashMap<>();
		for (final Term disjunct : disjuncts) {
			if (SmtUtils.isFalseLiteral(disjunct)) {
				continue;
			}
			final BucketKey bucket = determineBucket(disjunct, policy);
			if (bucket == null) {
				return null;
			}
			bucketTerms.computeIfAbsent(bucket, __ -> new ArrayList<>()).add(disjunct);
		}
		final Map<BucketKey, IPredicate> buckets = new LinkedHashMap<>();
		for (final var entry : bucketTerms.entrySet()) {
			buckets.put(entry.getKey(), mTools.orT(entry.getValue()));
		}
		return buckets;
	}

	private BucketKey determineBucket(final Term disjunct, final GuardBucketPolicy policy) {
		Integer selectedBucket = null;
		final List<Term> conjuncts = new ArrayList<>();
		InterferenceUtils.collectConjuncts(disjunct, conjuncts);
		for (final Term conjunct : conjuncts) {
			final Integer rawValue = extractRawIntEqualityValue(conjunct, policy.bucketVariable());
			if (rawValue == null) {
				continue;
			}
			final Integer bucket = policy.bucketForRawValue(rawValue);
			if (bucket == null) {
				return null;
			}
			if (selectedBucket == null) {
				selectedBucket = bucket;
			} else if (!selectedBucket.equals(bucket)) {
				return null;
			}
		}
		if (selectedBucket == null) {
			return null;
		}
		return new BucketKey(selectedBucket);
	}

	private Integer extractRawIntEqualityValue(final Term conjunct, final TermVariable bucketVariable) {
		if (!(conjunct instanceof final ApplicationTerm app) || !"=".equals(app.getFunction().getName())
				|| app.getParameters().length != 2) {
			return null;
		}
		final Integer fromLeft =
				extractIfVarEqualsConstant(app.getParameters()[0], app.getParameters()[1], bucketVariable);
		if (fromLeft != null) {
			return fromLeft;
		}
		return extractIfVarEqualsConstant(app.getParameters()[1], app.getParameters()[0], bucketVariable);
	}

	private static Integer extractIfVarEqualsConstant(final Term maybeVar, final Term maybeConst,
			final TermVariable bucketVariable) {
		if (maybeConst.getFreeVars().length != 0) {
			return null;
		}
		final Integer constant = parseIntConstant(maybeConst);
		if (constant == null) {
			return null;
		}
		if (bucketVariable.equals(maybeVar)) {
			return constant;
		}
		final Integer offset = extractBucketVariableOffset(maybeVar, bucketVariable);
		if (offset == null) {
			return null;
		}
		try {
			return Math.subtractExact(constant, offset);
		} catch (final ArithmeticException ex) {
			return null;
		}
	}

	private static Integer extractBucketVariableOffset(final Term term, final TermVariable bucketVariable) {
		if (bucketVariable.equals(term)) {
			return Integer.valueOf(0);
		}
		if (!(term instanceof final ApplicationTerm app)) {
			return null;
		}
		final String function = app.getFunction().getName();
		if ("+".equals(function) && app.getParameters().length == 2) {
			final Integer leftConst = parseIntConstant(app.getParameters()[0]);
			if (leftConst != null && bucketVariable.equals(app.getParameters()[1])) {
				return leftConst;
			}
			final Integer rightConst = parseIntConstant(app.getParameters()[1]);
			if (rightConst != null && bucketVariable.equals(app.getParameters()[0])) {
				return rightConst;
			}
			return null;
		}
		if ("-".equals(function) && app.getParameters().length == 2 && bucketVariable.equals(app.getParameters()[0])) {
			final Integer offset = parseIntConstant(app.getParameters()[1]);
			if (offset == null) {
				return null;
			}
			try {
				return Math.negateExact(offset);
			} catch (final ArithmeticException ex) {
				return null;
			}
		}
		if ("to_real".equals(function) && app.getParameters().length == 1) {
			return extractBucketVariableOffset(app.getParameters()[0], bucketVariable);
		}
		return null;
	}

	private static Integer parseIntConstant(final Term constantTerm) {
		if (constantTerm instanceof final ConstantTerm constant) {
			return rationalToInt(SmtUtils.toRational(constant));
		}
		if (constantTerm instanceof final ApplicationTerm app && app.getParameters().length == 1) {
			if ("-".equals(app.getFunction().getName())) {
				final Integer positiveValue = parseIntConstant(app.getParameters()[0]);
				if (positiveValue == null) {
					return null;
				}
				try {
					return Math.negateExact(positiveValue);
				} catch (final ArithmeticException ex) {
					return null;
				}
			}
			if ("to_real".equals(app.getFunction().getName())) {
				return parseIntConstant(app.getParameters()[0]);
			}
		}
		return null;
	}

	private static Integer rationalToInt(final Rational rational) {
		if (!BigInteger.ONE.equals(rational.denominator())) {
			return null;
		}
		try {
			return rational.numerator().intValueExact();
		} catch (final ArithmeticException ex) {
			return null;
		}
	}

	private IPredicate composeBuckets(final Map<BucketKey, IPredicate> buckets, final GuardBucketPolicy policy) {
		if (buckets.isEmpty()) {
			return mTools.bottom();
		}
		final List<Term> disjuncts = new ArrayList<>();
		for (final var entry : buckets.entrySet()) {
			if (entry.getValue() == null || SmtUtils.isFalseLiteral(entry.getValue().getFormula())) {
				continue;
			}
			disjuncts.add(mTools.andT(createBucketGuard(policy, entry.getKey()), entry.getValue().getFormula()).getFormula());
		}
		if (disjuncts.isEmpty()) {
			return mTools.bottom();
		}
		return mTools.orT(disjuncts);
	}

	private Term createBucketGuard(final GuardBucketPolicy policy, final BucketKey bucketKey) {
		return createLocationBucketGuard(policy, bucketKey.locationBucket());
	}

	private Term createLocationBucketGuard(final GuardBucketPolicy policy, final int bucket) {
		final Script script = mTools.getScript();
		final Collection<Integer> rawValues = policy.rawValuesForBucket(bucket);
		final List<Term> disjuncts = new ArrayList<>(rawValues.size());
		for (final Integer rawValue : rawValues) {
			disjuncts.add(SmtUtils.binaryEquality(script, policy.bucketVariable(), script.numeral(BigInteger.valueOf(rawValue))));
		}
		if (disjuncts.isEmpty()) {
			return script.term("false");
		}
		if (disjuncts.size() == 1) {
			return disjuncts.get(0);
		}
		return SmtUtils.or(script, disjuncts);
	}

}
