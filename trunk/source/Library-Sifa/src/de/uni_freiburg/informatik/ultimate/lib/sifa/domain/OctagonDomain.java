package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.WeakHashMap;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.RewriteEqualityTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class OctagonDomain implements IDomain {
	private final ILogger mLogger;
	private final SymbolicTools mTools;
	private final int mMaxDisjuncts;
	private final Supplier<IProgressAwareTimer> mTimeout;

	private final WeakHashMap<IPredicate, List<OctagonState>> mPredicateCache = new WeakHashMap<>();

	public OctagonDomain(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> timeout) {
		mTools = tools;
		mLogger = logger;
		mMaxDisjuncts = maxDisjuncts;
		mTimeout = timeout;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		// TODO using return mTools.or(lhs, rhs) is still an option.
		// Should we use it sometimes (for instance when inputs are not already cached)?
		List<OctagonState> joined = new ArrayList<>();
		joined.addAll(toOctagons(lhs));
		joined.addAll(toOctagons(rhs));
		if (joined.size() > mMaxDisjuncts) {
			joined = List.of(joinToSingleState(joined));
		}
		return toPredicate(joined);
	}

	private static OctagonState joinToSingleState(final List<OctagonState> states) {
		return states.stream().reduce(OctagonState::join).orElseThrow();
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		final List<OctagonState> oldStates = toOctagons(old);
		final List<OctagonState> widenWithStates = toOctagons(widenWith);
		final int productSize = oldStates.size() * widenWithStates.size();
		List<OctagonState> resultStates;
		if (productSize > mMaxDisjuncts) {
			final OctagonState oldState = joinToSingleState(oldStates);
			final OctagonState widenWithState = joinToSingleState(widenWithStates);
			resultStates = List.of(oldState.widen(widenWithState));
		} else {
			resultStates = new ArrayList<>(productSize);
			for (final OctagonState s1 : oldStates) {
				for (final OctagonState s2 : widenWithStates) {
					resultStates.add(s1.widen(s2));
				}
			}
		}
		return toPredicate(resultStates);
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
		return mPredicateCache.computeIfAbsent(pred, this::computeOctagons);
	}

	private List<OctagonState> computeOctagons(final IPredicate pred) {
		if (SmtUtils.isFalseLiteral(pred.getFormula())) {
			return List.of();
		}
		final IProgressAwareTimer timer = mTimeout.get();
		// TODO consider removing boolean sub-terms before computing DNF as we don't use the boolean terms anyways
		final Term[] disjuncts =
				mTools.dnfDisjuncts(pred, new RewriteEqualityTransformer(mTools.getScript())::transform);
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
