package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class BridgePairs<P> {
	HashRelation<Pair<Territory<P>, P>, Set<Region<P>>> mBridges;

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
	public <L> boolean addBridge(final Pair<Territory<P>, P> bridgePair, final Pair<Territory<P>, P> predecessor,
			final Transition<L, P> transition) {
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
	public <L> boolean isNecessaryBridge(final Pair<Territory<P>, P> pair, final Transition<L, P> transition) {
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
