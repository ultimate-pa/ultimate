package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class AbstractLocationPartitionedDomain implements IDomain, IThreadLocalDomainContext {
	private static final Map<String, Term> UNKNOWN = Map.of();

	private final IDomain mUnderlyingDomain;
	private final SymbolicTools mTools;
	private final Set<String> mLocVarNames;
	private final int mMaxBuckets;
	private final int mMaxDisjunctsPerBucket;
	private final WeakHashMap<IPredicate, Map<Map<String, Term>, IPredicate>> mBucketCache = new WeakHashMap<>();

	private AbstractLocationPartitionedDomain(final IDomain underlying, final SymbolicTools tools,
			final Set<String> locVarNames, final int maxBuckets, final int maxDisjunctsPerBucket) {
		mUnderlyingDomain = underlying;
		mTools = tools;
		mLocVarNames = Set.copyOf(locVarNames);
		mMaxBuckets = maxBuckets;
		mMaxDisjunctsPerBucket = maxDisjunctsPerBucket;
	}

	public static AbstractLocationPartitionedDomain create(final IDomain underlying, final SymbolicTools tools,
			final Map<String, TermVariable> locVarsByThread, final int maxBuckets, final int maxDisjunctsPerBucket) {
		final Set<String> names = new LinkedHashSet<>();
		locVarsByThread.values().forEach(tv -> names.add(tv.getName()));
		return new AbstractLocationPartitionedDomain(underlying, tools, names, maxBuckets, maxDisjunctsPerBucket);
	}

	@Override
	public void setCurrentThreadId(final String threadId) {
		if (mUnderlyingDomain instanceof final IThreadLocalDomainContext ctx) {
			ctx.setCurrentThreadId(threadId);
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
	public IPredicate alpha(final IPredicate pred) {
		return mUnderlyingDomain.alpha(pred);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		return mUnderlyingDomain.isEqBottom(pred);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		return mUnderlyingDomain.isSubsetEq(subset, superset);
	}

	private IPredicate combine(final IPredicate lhs, final IPredicate rhs, final BinaryOperator<IPredicate> op) {
		final Map<Map<String, Term>, IPredicate> left = bucketize(lhs);
		final Map<Map<String, Term>, IPredicate> right = bucketize(rhs);
		final Set<Map<String, Term>> keys = new LinkedHashSet<>(left.keySet());
		keys.addAll(right.keySet());
		final List<Term> disjuncts = new ArrayList<>();
		for (final Map<String, Term> key : keys) {
			final IPredicate l = left.get(key);
			final IPredicate r = right.get(key);
			final IPredicate combined;
			if (l == null) {
				combined = r;
			} else if (r == null) {
				combined = l;
			} else {
				combined = op.apply(l, r);
			}
			if (!SmtUtils.isFalseLiteral(combined.getFormula())) {
				disjuncts.add(combined.getFormula());
			}
		}
		if (disjuncts.isEmpty()) {
			return mTools.bottom();
		}
		return mTools.orT(disjuncts);
	}

	private Map<Map<String, Term>, IPredicate> bucketize(final IPredicate pred) {
		return mBucketCache.computeIfAbsent(pred, this::computeBuckets);
	}

	private Map<Map<String, Term>, IPredicate> computeBuckets(final IPredicate pred) {
		final Map<Map<String, Term>, List<Term>> groups = new LinkedHashMap<>();
		for (final Term disjunct : mTools.dnfDisjuncts(pred)) {
			groups.computeIfAbsent(keyOf(disjunct), k -> new ArrayList<>()).add(disjunct);
		}
		foldSurplusBucketsIntoCatchAll(groups);
		final Map<Map<String, Term>, IPredicate> result = new LinkedHashMap<>();
		groups.forEach((key, terms) -> result.put(key, capDisjuncts(terms)));
		return result;
	}

	private Map<String, Term> keyOf(final Term disjunct) {
		final Map<String, Term> key = new LinkedHashMap<>();
		for (final Term conjunct : SmtUtils.getConjuncts(disjunct)) {
			addLocationEquality(key, conjunct);
		}
		return Map.copyOf(key);
	}

	private void addLocationEquality(final Map<String, Term> key, final Term conjunct) {
		final ApplicationTerm appl = SmtUtils.getFunctionApplication(conjunct, "=");
		if (appl == null) {
			return;
		}
		final Term[] params = appl.getParameters();
		String locVarName = null;
		Term constant = null;
		for (final Term param : params) {
			if (param instanceof final TermVariable tv && mLocVarNames.contains(tv.getName())) {
				locVarName = tv.getName();
			} else if (param instanceof ConstantTerm) {
				constant = param;
			}
		}
		if (locVarName != null && constant != null) {
			key.put(locVarName, constant);
		}
	}

	private void foldSurplusBucketsIntoCatchAll(final Map<Map<String, Term>, List<Term>> groups) {
		final List<Map<String, Term>> keyed = new ArrayList<>();
		for (final Map<String, Term> key : groups.keySet()) {
			if (!key.isEmpty()) {
				keyed.add(key);
			}
		}
		if (keyed.size() <= mMaxBuckets) {
			return;
		}
		keyed.sort(Comparator.comparing(AbstractLocationPartitionedDomain::canonicalKey));
		final List<Term> catchAll = groups.computeIfAbsent(UNKNOWN, k -> new ArrayList<>());
		for (final Map<String, Term> surplus : keyed.subList(mMaxBuckets, keyed.size())) {
			catchAll.addAll(groups.remove(surplus));
		}
	}

	private static String canonicalKey(final Map<String, Term> key) {
		return key.entrySet().stream().sorted(Map.Entry.comparingByKey()).map(e -> e.getKey() + "=" + e.getValue())
				.collect(Collectors.joining(";"));
	}

	private IPredicate capDisjuncts(final List<Term> terms) {
		if (terms.size() <= mMaxDisjunctsPerBucket) {
			return mTools.orT(terms);
		}
		final List<IPredicate> preds = new ArrayList<>(terms.size());
		terms.forEach(t -> preds.add(mTools.predicate(t)));
		final List<Term> joined = new ArrayList<>(mMaxDisjunctsPerBucket);
		int sourceIdx = 0;
		for (int targetIdx = 0; targetIdx < mMaxDisjunctsPerBucket; targetIdx++) {
			final int remainingTargets = mMaxDisjunctsPerBucket - targetIdx;
			final int groupSize = (int) Math.ceil((preds.size() - sourceIdx) / (double) remainingTargets);
			IPredicate acc = preds.get(sourceIdx);
			for (int i = sourceIdx + 1; i < sourceIdx + groupSize; i++) {
				acc = mUnderlyingDomain.join(acc, preds.get(i));
			}
			joined.add(acc.getFormula());
			sourceIdx += groupSize;
		}
		return mTools.orT(joined);
	}
}
