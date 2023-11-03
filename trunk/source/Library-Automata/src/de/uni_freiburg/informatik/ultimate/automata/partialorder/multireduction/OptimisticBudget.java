/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.AcceptingRunSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.ReachabilityCheckVisitor;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Optimistic budget function for {@link SleepMapReduction}: First tries allocating a low budget, and checks if this
 * leads to an undesired automaton (typically, to reaching an accepting state). If so, the budget is increased
 * step-by-step.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states in the unreduced automaton
 * @param <R>
 *            The type of states in the reduced automaton
 */
public class OptimisticBudget<L, S, R> implements IBudgetFunction<L, R> {
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final IDfsOrder<L, R> mOrder;
	private final ISleepMapStateFactory<L, S, R> mStateFactory;
	private final Supplier<IDfsVisitor<L, R>> mMakeVisitor;

	private final SleepMapReduction<L, ?, R> mReduction;

	// A state is "successful" if no bad state is reachable from it
	private final Set<R> mSuccessful = new HashSet<>();
	// A state is "unsuccessful" if a bad state is reachable from it
	private final Set<R> mUnsuccessful = new HashSet<>();

	/**
	 *
	 * @param services
	 * @param order
	 *            The order in which the reduction automaton will be traversed
	 * @param stateFactory
	 *            The state factory used to create the reduction automaton
	 * @param makeVisitor
	 *            Creates a new visitor to determine reachability of "bad states" (the definition of bad states is up to
	 *            the caller). The visitor must either be an {@link AcceptingRunSearchVisitor} or a wrapper visitor such
	 *            that the underlying base visitor is an {@link AcceptingRunSearchVisitor}.
	 * @param reduction
	 *            The reduction automaton for which budgets shall be computed.
	 */
	public OptimisticBudget(final AutomataLibraryServices services, final IDfsOrder<L, R> order,
			final ISleepMapStateFactory<L, S, R> stateFactory, final Supplier<IDfsVisitor<L, R>> makeVisitor,
			final SleepMapReduction<L, ?, R> reduction) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(OptimisticBudget.class);
		mOrder = order;
		mStateFactory = stateFactory;
		mMakeVisitor = makeVisitor;
		mReduction = reduction;
	}

	@Override
	public int computeBudget(final R state, final L letter) {
		if (mReduction == null) {
			throw new UnsupportedOperationException(
					"Optimistic budget cannot be used without setting reduction automaton");
		}

		mLogger.debug("Determining budget for %s under input %s", state, letter);

		final SleepMap<L, S> sleepMap = mStateFactory.getSleepMap(state);
		int maximumBudget;
		if (sleepMap.contains(letter)) {
			// Never return a budget higher than the price in the sleep map.
			// Because the reduction considers the minimum of the two values, this would be pointless.
			maximumBudget = sleepMap.getPrice(letter);
			assert maximumBudget <= mStateFactory.getBudget(state) : "invalid state: " + state;
		} else {
			// Ensure invariant for budget functions: Must never exceed budget of the current state.
			maximumBudget = mStateFactory.getBudget(state);
		}
		mLogger.debug("maximum budget: %d", maximumBudget);

		// Find the least budget that is successful.
		for (int budget = 0; budget < maximumBudget; ++budget) {
			mLogger.debug("trying with budget %d", budget);
			final R successor = mReduction.computeSuccessorWithBudget(state, letter, budget);
			if (successor == null) {
				mLogger.debug("No successor for given letter exists");
				break;
			}

			mLogger.debug("running nested DFS from %s under input %s with assumed budget %d", state, letter, budget);
			if (isSuccessful(successor)) {
				mLogger.debug("determined budget %d for %s under input %s", budget, state, letter);
				return budget;
			}
		}

		// We fall back to returning the maximum budget.
		mLogger.debug("determined budget %d (max) for %s under input %s", maximumBudget, state, letter);
		return maximumBudget;
	}

	private boolean isSuccessful(final R state) {
		// TODO Caching should take into account monotonicity (if it holds); perhaps use covering to achieve this

		if (mSuccessful.contains(state)) {
			return true;
		}
		if (mUnsuccessful.contains(state)) {
			return false;
		}

		final boolean result = checkIsSuccessful(state);
		assert (result && mSuccessful.contains(state)) || (!result && mUnsuccessful.contains(state));
		return result;
	}

	private boolean checkIsSuccessful(final R state) {
		// If we can reach a known unsuccessful state, the given state is definitely unsuccessful.
		// Hence we can abort the search. To this end, we use a ReachabilityCheckVisitor.
		final var visitor = new ReachabilityCheckVisitor<>(mMakeVisitor.get(), mUnsuccessful, mSuccessful);

		try {
			new DepthFirstTraversal<>(mServices, mReduction, mOrder, visitor, state);
		} catch (final AutomataOperationCanceledException e) {
			throw new ToolchainCanceledException(getClass());
		}

		final IRun<L, R> run = ((AcceptingRunSearchVisitor<L, R>) visitor.getBaseVisitor()).getAcceptingRun();
		if (run != null) {
			// We found an entire accepting run. Hence we are not successful, and neither is any state on this run.
			mUnsuccessful.addAll(run.getStateSequence());
			return false;
		}

		// We did not find an accepting run. Hence we are successful iff we did not reach a known unsuccessful state.
		final boolean result = !visitor.reachabilityConfirmed();
		if (result) {
			mSuccessful.add(state);
		} else {
			// The visitor is expected to add all states on the stack to this set.
			assert mUnsuccessful.contains(state);
		}
		return result;
	}
}
