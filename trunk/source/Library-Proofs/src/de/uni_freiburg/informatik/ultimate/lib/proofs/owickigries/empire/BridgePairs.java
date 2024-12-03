/*
 * Copyright (C) 2024 Matthias Zumkeller
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class BridgePairs<P> {
	HashRelation<Pair<Territory<P>, IPredicate>, Set<Region<P>>> mBridges;

	public BridgePairs() {
		mBridges = new HashRelation<>();
	}

	private boolean bystanderExtended(final Set<Region<P>> bystanders, final Set<P> predecessors) {
		return bystanders.stream()
				.anyMatch(bystander -> !DataStructureUtils.haveEmptyIntersection(bystander.getPlaces(), predecessors));
	}

	/**
	 * Add a bridge pair. The function checks if the input pair actually is a bridge pair and stores it if so.
	 *
	 * @param <L>
	 * @param bridgePair
	 *            Bridge Pair
	 * @param predecessor
	 *            Predecessor pair for the given transition
	 * @param transition
	 *            Transition that leads to the bridge pair.
	 * @return True if the pair is a bridge and was successfully added, false otherwise.
	 */
	public <L> boolean addBridge(final Pair<Territory<P>, IPredicate> bridgePair,
			final Pair<Territory<P>, IPredicate> predecessor, final Transition<L, P> transition) {
		final var territory = predecessor.getFirst();
		final var predecessors = transition.getPredecessors();
		final var bystanders = territory.getRegions().stream()
				.filter(r -> DataStructureUtils.haveEmptyIntersection(r.getPlaces(), predecessors))
				.collect(Collectors.toSet());
		if (bystanders.isEmpty()) {
			return false;
		}
		mBridges.addPair(bridgePair, bystanders);
		return true;
	}

	/**
	 * Check if a (bridge-) pair is necessary i.e. check if an extension of the pair would lead to a breach of the
	 * bystander condition.
	 *
	 * @param <L>
	 * @param pair
	 *            Pair that will be extended
	 * @param transition
	 *            Transition for which the pair gets extended
	 * @return True if the pair is necessary and false otherwise.
	 */
	public <L> boolean isNecessaryBridge(final Pair<Territory<P>, IPredicate> pair, final Transition<L, P> transition) {
		final var predecessors = transition.getPredecessors();
		final var successors = transition.getSuccessors();
		if (pair.getFirst().getPlaces().containsAll(successors)) {
			return false;
		}
		final var bystanderSet = mBridges.getImage(pair);
		for (final Set<Region<P>> bystanders : bystanderSet) {
			if (bystanderExtended(bystanders, predecessors)) {
				return true;
			}
		}
		return false;
	}
}
