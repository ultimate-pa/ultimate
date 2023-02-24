package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class OctagonDomain implements IDomain {
	private final ILogger mLogger;
	private final SymbolicTools mTools;
	private final int mMaxDisjuncts;
	private final Supplier<IProgressAwareTimer> mTimeout;

	public OctagonDomain(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> timeout) {
		mTools = tools;
		mLogger = logger;
		mMaxDisjuncts = maxDisjuncts;
		mTimeout = timeout;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		// TODO: Should we convert this to octagons instead?
		return mTools.or(lhs, rhs);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		// TODO: Use actual widening that reaches a fixpoint!
		return mTools.or(old, widenWith);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		return RelationCheckUtil.isEqBottom_SolverAlphaSolver(mTools, this, pred);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		return RelationCheckUtil.isSubsetEq_SolverAlphaSolver(mTools, this, subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		return toPredicate(toOctagons(pred));
	}

	private IPredicate toPredicate(final Collection<OctagonState> states) {
		return mTools.orT(states.stream().map(x -> x.toTerm(mTools.getScript())).collect(Collectors.toList()));
	}

	private List<OctagonState> toOctagons(final IPredicate pred) {
		final IProgressAwareTimer timer = mTimeout.get();
		// TODO consider removing boolean sub-terms before computing DNF as we don't use the boolean terms anyways
		final Term[] disjuncts = mTools.dnfDisjuncts(pred);
		final List<OctagonState> result = new ArrayList<>(disjuncts.length);
		for (final Term dnfDisjunct : disjuncts) {
			if (!timer.continueProcessing()) {
				mLogger.warn("Interval domain alpha timed out before all disjuncts were processed. "
						+ "Continuing with top.");
				return List.of(OctagonState.TOP);
			}
			final OctagonState state = OctagonState.from(dnfDisjunct, mTools.getScript());
			if (state != null) {
				result.add(state);
			}
		}
		// TODO join disjuncts if there are too many of them
		return result;
	}
}
