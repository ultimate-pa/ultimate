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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class AbstractStateBasedDomain<STATE extends IAbstractState<STATE>> implements IDomain {
	protected final ILogger mLogger;
	protected final SymbolicTools mTools;
	private final int mMaxDisjuncts;
	private final Supplier<IProgressAwareTimer> mTimeout;
	private final WeakHashMap<IPredicate, List<STATE>> mPredicateCache = new WeakHashMap<>();

	public AbstractStateBasedDomain(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
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
		List<STATE> joined = new ArrayList<>();
		joined.addAll(toStates(lhs));
		joined.addAll(toStates(rhs));
		if (joined.size() > mMaxDisjuncts) {
			joined = List.of(joinToSingleState(joined));
		}
		return toPredicate(joined);
	}

	private STATE joinToSingleState(final List<STATE> states) {
		return states.stream().reduce(STATE::join).orElseThrow();
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		final List<STATE> oldStates = toStates(old);
		final List<STATE> widenWithStates = toStates(widenWith);
		final int productSize = oldStates.size() * widenWithStates.size();
		List<STATE> resultStates;
		if (productSize > mMaxDisjuncts) {
			final STATE oldState = joinToSingleState(oldStates);
			final STATE widenWithState = joinToSingleState(widenWithStates);
			resultStates = List.of(oldState.widen(widenWithState));
		} else {
			resultStates = new ArrayList<>(productSize);
			for (final STATE s1 : oldStates) {
				for (final STATE s2 : widenWithStates) {
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
		return toPredicate(toStates(pred));
	}

	private List<STATE> toStates(final IPredicate pred) {
		return mPredicateCache.computeIfAbsent(pred, this::computeStates);
	}

	private List<STATE> computeStates(final IPredicate pred) {
		final IProgressAwareTimer timer = mTimeout.get();
		final Term[] disjuncts = mTools.dnfDisjuncts(pred, this::transformTerm);
		final List<STATE> result = new ArrayList<>(disjuncts.length);
		for (final Term dnfDisjunct : disjuncts) {
			if (!timer.continueProcessing()) {
				mLogger.warn(getClass().getSimpleName()
						+ " alpha timed out before all disjuncts were processed. Continuing with top.");
				return List.of(getTopState());
			}
			if (SmtUtils.isFalseLiteral(dnfDisjunct)) {
				continue;
			}
			final STATE state = toState(SmtUtils.getConjuncts(dnfDisjunct));
			if (state != null) {
				result.add(state);
			}
		}
		// TODO join disjuncts if there are too many of them
		return result;
	}

	protected Term transformTerm(final Term term) {
		return term;
	}

	private IPredicate toPredicate(final Collection<STATE> states) {
		return mTools.orT(states.stream().map(x -> x.toTerm(mTools.getScript())).collect(Collectors.toList()));
	}

	public abstract STATE toState(Term[] conjuncts);

	public abstract STATE getTopState();

}
