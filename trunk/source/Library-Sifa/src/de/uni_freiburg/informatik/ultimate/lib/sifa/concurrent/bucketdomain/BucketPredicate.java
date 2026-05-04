package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class BucketPredicate implements IPredicate {
	private final Map<Integer, IPredicate> mBuckets;
	private final IPredicate mComposed;

	private BucketPredicate(final Map<Integer, IPredicate> buckets, final IPredicate composed) {
		mBuckets = Map.copyOf(buckets);
		mComposed = composed;
	}

	public static BucketPredicate of(final SymbolicTools tools, final Map<Integer, IPredicate> buckets) {
		final Map<Integer, IPredicate> nonEmpty = new LinkedHashMap<>();
		final var disjuncts = new ArrayList<Term>();
		for (final var entry : buckets.entrySet()) {
			if (!SmtUtils.isFalseLiteral(entry.getValue().getFormula())) {
				nonEmpty.put(entry.getKey(), entry.getValue());
				disjuncts.add(entry.getValue().getFormula());
			}
		}
		return new BucketPredicate(nonEmpty, disjuncts.isEmpty() ? tools.bottom() : tools.orT(disjuncts));
	}

	public Map<Integer, IPredicate> buckets() {
		return mBuckets;
	}

	@Override
	public Term getFormula() {
		return mComposed.getFormula();
	}

	@Override
	public Term getClosedFormula() {
		return mComposed.getClosedFormula();
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mComposed.getVars();
	}

	@Override
	public Set<IProgramFunction> getFuns() {
		return mComposed.getFuns();
	}

	@Override
	public String toString() {
		return mBuckets.toString();
	}
}
