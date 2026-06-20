package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class AbstractLocationPartitionedPredicate implements IPredicate {
	private final Map<GlobalLocationState, IPredicate> mPartitions;
	private final IPredicate mComposed;

	private AbstractLocationPartitionedPredicate(final Map<GlobalLocationState, IPredicate> partitions, final IPredicate composed) {
		mPartitions = Map.copyOf(partitions);
		mComposed = composed;
	}

	static AbstractLocationPartitionedPredicate create(final Map<GlobalLocationState, IPredicate> nonEmptyPartitions,
			final IPredicate composed) {
		return new AbstractLocationPartitionedPredicate(nonEmptyPartitions, composed);
	}

	public Map<GlobalLocationState, IPredicate> partitions() {
		return mPartitions;
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
		return mPartitions.toString();
	}
}
