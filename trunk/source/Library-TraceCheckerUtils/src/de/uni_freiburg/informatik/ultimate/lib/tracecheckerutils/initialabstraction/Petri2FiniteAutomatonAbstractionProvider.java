/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.LazyPetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.HoareProofSettings;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Transforms an initial abstraction in the form of a Petri net to a finite automaton.
 *
 * This class is abstract. Users should pick one of the concrete subclasses {@link Eager} or {@link Lazy} as required.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of transitions
 * @param <A>
 *            The type of automaton that is provided
 */
public abstract class Petri2FiniteAutomatonAbstractionProvider<L extends IIcfgTransition<?>, A extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
		implements IInitialAbstractionProvider<L, A> {

	protected final IInitialAbstractionProvider<L, ? extends IPetriNet<L, IPredicate>> mUnderlying;
	protected final IUltimateServiceProvider mServices;
	protected final AutomataLibraryServices mAutomataServices;
	protected final IPetriNet2FiniteAutomatonStateFactory<IPredicate> mStateFactory;

	public Petri2FiniteAutomatonAbstractionProvider(final IUltimateServiceProvider services,
			final IInitialAbstractionProvider<L, ? extends IPetriNet<L, IPredicate>> underlying,
			final IPetriNet2FiniteAutomatonStateFactory<IPredicate> stateFactory) {
		mUnderlying = underlying;
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(services);
		mStateFactory = stateFactory;
	}

	/**
	 * Determines if the locations belonging to the given marking are all hopeless. In this case, the state
	 * corresponding to this marking can be omitted from the program automaton.
	 */
	protected static boolean areAllLocationsHopeless(final Map<IcfgLocation, Boolean> hopelessCache,
			final Set<? extends IcfgLocation> errorLocs, final Marking<IPredicate> marking) {
		for (final IPredicate place : marking) {
			if (place instanceof ISLPredicate) {
				final IcfgLocation location = ((ISLPredicate) place).getProgramPoint();
				if (!isLocationHopeless(hopelessCache, errorLocs, location)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * A location is hopeless if in the CFG there is no path from this location to an error location.
	 */
	private static boolean isLocationHopeless(final Map<IcfgLocation, Boolean> hopelessCache,
			final Set<? extends IcfgLocation> errorLocs, final IcfgLocation loc) {
		if (errorLocs.contains(loc)) {
			return false;
		}
		return !IcfgUtils.canReachCached(loc, e -> errorLocs.contains(e.getTarget()), e -> false, l -> {
			if (!hopelessCache.containsKey(l)) {
				return LBool.UNKNOWN;
			}
			return hopelessCache.get(l) ? LBool.SAT : LBool.UNSAT;
		}, (l, res) -> {
			assert hopelessCache.getOrDefault(l, res) == res : "contradictory reachability";
			assert res != null;
			hopelessCache.put(l, res);
		});
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mUnderlying.getStatistics();
	}

	/**
	 * Transforms an initial abstraction in the form of a Petri net to a finite automaton, by eagerly exploring and
	 * explicitly constructing all reachable states of the reachability graph.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of transitions
	 */
	public static class Eager<L extends IIcfgTransition<?>>
			extends Petri2FiniteAutomatonAbstractionProvider<L, INestedWordAutomaton<L, IPredicate>> {
		private INestedWordAutomaton<L, IPredicate> mAbstraction;
		private CfgSmtToolkit mCsToolkit;

		/**
		 * Create a new instance of the provider.
		 *
		 * @param underlying
		 *            The underlying provider whose abstraction is transformed to a finite automaton
		 * @param stateFactory
		 *            The state factory used to create the automaton states
		 * @param services
		 *            services used in the transformation
		 */
		public Eager(final IUltimateServiceProvider services,
				final IInitialAbstractionProvider<L, ? extends IPetriNet<L, IPredicate>> underlying,
				final IPetriNet2FiniteAutomatonStateFactory<IPredicate> stateFactory) {
			super(services, underlying, stateFactory);
		}

		@Override
		public INestedWordAutomaton<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
				final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
			mCsToolkit = icfg.getCfgSmtToolkit();

			final IPetriNet<L, IPredicate> net = mUnderlying.getInitialAbstraction(icfg, errorLocs);
			try {
				final Map<IcfgLocation, Boolean> hopelessCache = new HashMap<>();
				mAbstraction = new PetriNet2FiniteAutomaton<>(mAutomataServices, mStateFactory, net,
						s -> areAllLocationsHopeless(hopelessCache, errorLocs, s)).getResult();
				mServices.getLoggingService().getLogger(getClass()).info(mAbstraction);
				return mAbstraction;
			} catch (final PetriNetNot1SafeException e) {
				final Collection<?> unsafePlaces = e.getUnsafePlaces();
				if (unsafePlaces == null) {
					throw new AssertionError("Unable to find Petri net place that violates 1-safety");
				}
				final ISLPredicate unsafePlace = (ISLPredicate) unsafePlaces.iterator().next();
				final String proc = unsafePlace.getProgramPoint().getProcedure();
				throw new IllegalStateException("Petrification does not provide enough thread instances for " + proc);
			}
		}

		public NwaHoareProofProducer<L> getProofProducer(final PredicateFactory predicateFactory,
				final HoareProofSettings hoarePrefs) {
			return new NwaHoareProofProducer<>(mServices, mAbstraction, mCsToolkit, predicateFactory, hoarePrefs,
					mAbstraction.getStates());
		}
	}

	/**
	 * Transforms an initial abstraction in the form of a Petri net to a finite automaton. Transitions and states in the
	 * automaton are created only on-demand, not eagerly.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of transitions
	 */
	public static class Lazy<L extends IIcfgTransition<?>>
			extends Petri2FiniteAutomatonAbstractionProvider<L, LazyPetriNet2FiniteAutomaton<L, IPredicate>> {

		/**
		 * Create a new instance.
		 *
		 * @param underlying
		 *            The underlying provider whose provided abstraction is transformed.
		 * @param stateFactory
		 *            The state factory used to create automaton states
		 * @param services
		 *            services used in the transformation
		 */
		public Lazy(final IUltimateServiceProvider services,
				final IInitialAbstractionProvider<L, ? extends IPetriNet<L, IPredicate>> underlying,
				final IPetriNet2FiniteAutomatonStateFactory<IPredicate> stateFactory) {
			super(services, underlying, stateFactory);
		}

		@Override
		public LazyPetriNet2FiniteAutomaton<L, IPredicate> getInitialAbstraction(
				final IIcfg<? extends IcfgLocation> icfg, final Set<? extends IcfgLocation> errorLocs)
				throws AutomataLibraryException {
			final IPetriNet<L, IPredicate> net = mUnderlying.getInitialAbstraction(icfg, errorLocs);
			final Map<IcfgLocation, Boolean> hopelessCache = new HashMap<>();
			return new LazyPetriNet2FiniteAutomaton<>(mAutomataServices, mStateFactory, net,
					s -> areAllLocationsHopeless(hopelessCache, errorLocs, s));
		}
	}
}
