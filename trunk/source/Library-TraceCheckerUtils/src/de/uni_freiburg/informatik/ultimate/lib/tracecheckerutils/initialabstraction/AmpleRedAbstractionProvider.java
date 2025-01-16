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
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.AmpleReductionConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.RandomDfsOrder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ThreadBasedPersistentSets;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;

/*
 * Analogon to PartialOrderAbstractionProvider
 *
 *
 *
 * @param <L>: type of transition
 *
 *
 */
// first transform the petrinet using the petrinet2finiteautomaton? then reduce?
public class AmpleRedAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, NestedWordAutomaton<L, IPredicate>> {

	private final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mUnderlying;
	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mStateFactory;
	private final long mDfsOrderSeed;
	private final AutomataLibraryServices mAutomataServices;

	// TODO: Do a check whether the input automaton is deterministic?
	public AmpleRedAbstractionProvider(
			final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> underlying,
			final IUltimateServiceProvider services, final IEmptyStackStateFactory<IPredicate> stateFactory,
			final long seed) {
		mUnderlying = underlying;
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(services);
		mStateFactory = stateFactory;
		mDfsOrderSeed = seed;
	}

	@Override
	public NestedWordAutomaton<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {

		final IIndependenceRelation<IPredicate, L> indep =
				IndependenceBuilder.<L> semantic(mServices, icfg.getCfgSmtToolkit().getManagedScript(), false, false)
						.withSyntacticCheck().cached().threadSeparated().build();
		// get persistent sets - should we give the error locs?
		final IPersistentSetChoice<L, IPredicate> persistent =
				new ThreadBasedPersistentSets(mServices, icfg, indep, null, errorLocs, true);
		// get visitor
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> originalAutomaton =
				mUnderlying.getInitialAbstraction(icfg, errorLocs);
		final AmpleReductionConstructingVisitor<L, IPredicate> visitor = new AmpleReductionConstructingVisitor<>(
				originalAutomaton, originalAutomaton::isInitial, originalAutomaton::isFinal,
				originalAutomaton.getVpAlphabet(), mAutomataServices, mStateFactory, persistent);
		// get reduction
		// as we assume a deterministic input automaton, there should only be one initial state here
		final IPredicate initState = originalAutomaton.getInitialStates().iterator().next();
		// TODO: Do something about the order (order shouldnt matter) // state here
		final AmpleReduction<L, IPredicate> ampleRed = new AmpleReduction<>(mAutomataServices, originalAutomaton,
				new RandomDfsOrder<>(mDfsOrderSeed, false), visitor, initState);

		return visitor.getReductionAutomaton();
	}

}
