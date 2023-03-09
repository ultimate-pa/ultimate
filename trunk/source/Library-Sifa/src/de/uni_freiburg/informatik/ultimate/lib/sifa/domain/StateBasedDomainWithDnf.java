package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class StateBasedDomainWithDnf<STATE extends IAbstractState<STATE>>
		extends StateBasedDomain<STATE> {
	public StateBasedDomainWithDnf(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> timeout) {
		super(logger, tools, maxDisjuncts, timeout);
	}

	@Override
	protected List<STATE> toStates(final IPredicate pred) {
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
			if (!state.isBottom()) {
				result.add(state);
			}
		}
		// TODO join disjuncts if there are too many of them
		return result;
	}

	/**
	 * Transformations that are applied before converting the DNF to improve the states that are produced from the DNF.
	 * This method has to return an overapproximation of {@code term}.
	 */
	protected Term transformTerm(final Term term) {
		return term;
	}

	/**
	 * Returns the internal state representation for the given conjuncts.
	 */
	protected abstract STATE toState(Term[] conjuncts);

	/**
	 * Returns the internal state that that represents top.
	 */
	protected abstract STATE getTopState();
}
