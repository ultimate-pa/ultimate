/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2019-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
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

/**
 * Abstract class for an {@link IDomain} that uses states, i.e. that transforms predicates into an internal state
 * representation (using the method {@code toStates}).
 *
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The abstract state that is used internally
 */
public class StateBasedDomain<STATE extends IAbstractState<STATE>> implements IDomain {
	private final SymbolicTools mTools;
	private final int mMaxDisjuncts;
	private final ILogger mLogger;
	private final Supplier<IProgressAwareTimer> mTimeout;
	private final IStateProvider<STATE> mStateProvider;
	// TODO: Is it good to use a WeakHashMap here?
	private final WeakHashMap<IPredicate, List<STATE>> mPredicateCache = new WeakHashMap<>();

	public StateBasedDomain(final SymbolicTools tools, final int maxDisjuncts, final ILogger logger,
			final Supplier<IProgressAwareTimer> timeout, final IStateProvider<STATE> stateProvider) {
		mTools = tools;
		mMaxDisjuncts = maxDisjuncts;
		mLogger = logger;
		mTimeout = timeout;
		mStateProvider = stateProvider;
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
		final Term[] disjuncts = mTools.dnfDisjuncts(pred, mStateProvider::preprocessTerm);
		final List<STATE> result = new ArrayList<>(disjuncts.length);
		for (final Term dnfDisjunct : disjuncts) {
			if (!timer.continueProcessing()) {
				mLogger.warn(getClass().getSimpleName()
						+ " alpha timed out before all disjuncts were processed. Continuing with top.");
				return List.of(mStateProvider.getTopState());
			}
			if (SmtUtils.isFalseLiteral(dnfDisjunct)) {
				continue;
			}
			final STATE state = mStateProvider.toState(SmtUtils.getConjuncts(dnfDisjunct));
			if (!state.isBottom()) {
				result.add(state);
			}
		}
		// TODO: Should we join the states if there are too many?
		return result;
	}

	private IPredicate toPredicate(final List<STATE> states) {
		return mTools.orT(states.stream().map(x -> x.toTerm(mTools.getScript())).collect(Collectors.toList()));
	}

	public interface IStateProvider<STATE extends IAbstractState<STATE>> {
		/**
		 * Returns the internal state representation for the given conjuncts.
		 */
		STATE toState(Term[] conjuncts);

		/**
		 * Returns the internal state that represents top.
		 */
		STATE getTopState();

		/**
		 * Transformations that are applied before converting the DNF to improve the states that are produced from the
		 * DNF. This method has to return an overapproximation of {@code term}.
		 */
		Term preprocessTerm(final Term term);
	}
}
