/*
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.directed;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Territory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.directed.DirectedEmpire.State;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

// Matthias Z (2026-06-06): Maybe this class should implement the IEmpire interface?
// The structure is practically the same and the empire product should again be an empire.
public class DirectedEmpireProduct<L, P> {

	private final List<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> mEmpires;
	private final INestedWordAutomaton<Transition<L, P>, ProductState<L, P>> mProduct;
	private final IPetriNet<L, P> mNet;

	private final IUltimateServiceProvider mServices;

	public DirectedEmpireProduct(final List<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> empires,
			final IPetriNet<L, P> net, final IUltimateServiceProvider services) {
		mEmpires = empires;
		mNet = net;
		mServices = services;

		mProduct = constructProductAutomaton();
	}

	private ProductState<L, P> constructInitialState() {
		final var initialPlaces = mNet.getInitialPlaces();
		final var initStates =
				mEmpires.stream().flatMap(e -> e.getInitialStates().stream()).collect(Collectors.toList());
		final var initTerrs = initStates.stream().map(State::territory).collect(Collectors.toSet());
		final var interRegions = getIntersectionRegions(initialPlaces, initTerrs);
		final var initTerritory = new Territory<>(ImmutableSet.of(interRegions));
		return new ProductState<>(initStates, initTerritory);
	}

	private Set<Region<P>> getIntersectionRegions(final Set<P> places,
			final Set<Territory<P, ConnectedRegion<L, P>>> territories) {
		final var interRegions = new HashSet<Region<P>>();
		for (final P place : places) {
			final var regions = territories.stream().map(t -> t.getPlaceRegion(place)).collect(Collectors.toSet());
			final var inter = ConnectedRegion.intersectConnectedRegions(regions, place);
			interRegions.add(inter);
		}
		return interRegions;
	}

	// Matthias Z (2026-06-06): If this approach gets resumed in the future, this could also be done on-the-fly.
	private INestedWordAutomaton<Transition<L, P>, ProductState<L, P>> constructProductAutomaton() {
		final var alphabet = new VpAlphabet<>(mNet.getTransitions());
		final var product = new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), alphabet,
				() -> new ProductState<L, P>(null, null));
		final var init = constructInitialState();
		product.addState(true, false, init);
		final var queue = new ArrayDeque<ProductState<L, P>>();
		queue.add(init);
		while (!queue.isEmpty()) {
			final var currentState = queue.poll();
			final var enabledTransitions =
					currentState.intersectionTerritory().getEnabledTransitions(mNet).collect(Collectors.toSet());
			for (final Transition<L, P> transition : enabledTransitions) {
				final var succState = getSuccessorProductState(currentState.productStates, transition,
						currentState.intersectionTerritory.getBystanders(transition));
				if (succState == null) {
					continue;
				}
				if (!product.getStates().contains(succState)) {
					product.addState(false, false, succState);
					queue.offer(succState);
				}
				product.addInternalTransition(currentState, transition, succState);
			}
		}
		return product;
	}

	private ProductState<L, P> getSuccessorProductState(final List<State<L, P>> states,
			final Transition<L, P> transition, final Set<Region<P>> bystanders) {
		final var succStates = new ArrayList<State<L, P>>();
		for (int i = 0; i < states.size(); i++) {
			final var state = states.get(i);
			final var succIter = mEmpires.get(i).internalSuccessors(state, transition);
			if (!succIter.iterator().hasNext()) {
				return null;
			}
			final var succ = DataStructureUtils.getOneAndOnly(succIter, "Successor state");
			succStates.add(succ.getSucc());
		}

		assert succStates.size() == mEmpires.size() : "Not enough states in product state!";

		final var succTerritories = succStates.stream().map(State::territory).collect(Collectors.toSet());
		final var interRegions = getIntersectionRegions(transition.getSuccessors(), succTerritories);
		interRegions.addAll(bystanders);
		final var succTerr = new Territory<>(ImmutableSet.of(interRegions));
		return new ProductState<>(succStates, succTerr);
	}

	public INestedWordAutomaton<Transition<L, P>, ProductState<L, P>> getProductAutomaton() {
		return mProduct;
	}

	public record ProductState<L, P>(List<State<L, P>> productStates, Territory<P, Region<P>> intersectionTerritory,
			int hash) {
		// Convenience constructor that computes the correct hash code. Always use this constructor.
		public ProductState(final List<State<L, P>> productStates,
				final Territory<P, Region<P>> intersectionTerritory) {
			this(productStates, intersectionTerritory, Objects.hash(productStates, intersectionTerritory));
		}

		@Override
		public int hashCode() {
			return hash;
		}
	}
}
