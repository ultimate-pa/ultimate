/*
 * Copyright (C) 2025 Veronika Klasen
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AmpleReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.AutomatonConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ThreadBasedPersistentSets;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

/*
 * Analogon to PartialOrderAbstractionProvider, used for ample set reduction
 *
 *
 *
 * @param <L>: type of transition
 *
 *
 */
public class AmpleRedAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, NestedWordAutomaton<L, IPredicate>> {

	private final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mUnderlying;
	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mStateFactory;
	private final AutomataLibraryServices mAutomataServices;
	private final AmpleRedStatistics mStatistics;

	/**
	 * Create a new instance of the provider.
	 *
	 * @param underlying
	 *            The provider whose provided initial abstraction is then transformed by this instance
	 * @param services
	 *            Ultimate services used by Ample Set Reduction
	 * @param stateFactory
	 *            A state factory used by the reduced automaton
	 * @param seed
	 *            The seed to use for the random DFS order.
	 */
	public AmpleRedAbstractionProvider(
			final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> underlying,
			final IUltimateServiceProvider services, final IEmptyStackStateFactory<IPredicate> stateFactory) {
		mUnderlying = underlying;
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(services);
		mStateFactory = stateFactory;
		mStatistics = new AmpleRedStatistics();
	}

	@Override
	public NestedWordAutomaton<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {

		mStatistics.startTimer();
		final IIndependenceRelation<IPredicate, L> indep =
				IndependenceBuilder.<L> semantic(mServices, icfg.getCfgSmtToolkit().getManagedScript(), false, false)
						.withSyntacticCheck().cached().threadSeparated().build();
		// get persistent sets - do the error locations even matter?
		final IPersistentSetChoice<L, IPredicate> persistent =
				new ThreadBasedPersistentSets(mServices, icfg, indep, null, errorLocs, true);
		// get the automaton we want to reduce
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> originalAutomaton =
				mUnderlying.getInitialAbstraction(icfg, errorLocs);

		// We require the input automaton for ample set reduction to be deterministic and only contain final states
		final AutomatonConstructingVisitor<L, IPredicate> visitor =
				new AutomatonConstructingVisitor<>(originalAutomaton, mAutomataServices, mStateFactory);

		// get the reduction
		// as we assume a deterministic input automaton, there should only be one initial state here
		final IPredicate initState = originalAutomaton.getInitialStates().iterator().next();
		new AmpleReduction<>(mAutomataServices, originalAutomaton, ConstantDfsOrder.byHashCode(), visitor, initState,
				persistent);
		final NestedWordAutomaton<L, IPredicate> redAutomaton = visitor.getReductionAutomaton();
		mStatistics.stopTimer();
		mStatistics.mReductionStates = redAutomaton.getStates().size();
		mStatistics.mReductionTS = redAutomaton.computeNumberOfInternalTransitions();

		mServices.getLoggingService().getLogger(getClass())
				.info("Constructed initial ample set-reduced NBA abstraction that " + redAutomaton.sizeInformation());
		return redAutomaton;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	// Statistics for the whole ample set reduction
	private class AmpleRedStatistics extends AbstractStatisticsDataProvider {

		int mReductionTS = 0;
		int mReductionStates = 0;
		TimeTracker mReductionTime = new TimeTracker();

		public AmpleRedStatistics() {
			declareTimeTracker("Time to compute Ample Reduction", mReductionTime);
			declareCounter("Number of transitions in reduction automaton", () -> mReductionTS);
			declareCounter("Number of states in reduction automaton", () -> mReductionStates);
			forward("Underlying", mUnderlying::getStatistics);
		}

		public void startTimer() {
			mReductionTime.start();
		}

		public void stopTimer() {
			mReductionTime.stop();
		}
	}
}
