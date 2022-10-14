package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * A retromorphism relates firing sequences of two Petri nets, a "new" to an "old" net. It allows us to reason about
 * firing sequences of the new net by looking at a complete finite prefix of the unfolding for the old net.
 *
 * Conceptually, a retromorphism is a mapping from transitions of the new net back to non-empty sets of non-empty
 * (finite) sequences of transitions of the old net. This can be extended to a mapping from sequences of new transitions
 * to sets of sequences of old transitions by pointwise application and concatenation.
 *
 * A retromorphism alpha must satisfy the following conditions:
 *
 * (1) Let sigma be a sequence of old transitions, and sigma' a sequence of new transitions, such that sigma is an
 * element of alpha(sigma'). Then sigma is a firing sequence of the old net if and only if sigma' is a firing sequence
 * of the new net.
 *
 * (2) Let sigma be a firing sequence of the old net and sigma' a firing sequence of the new net, such that sigma is an
 * element of alpha(sigma'). Then sigma is accepting if and only if sigma' is accepting.
 *
 *
 * In practice, we do not represent the retromorphism alpha precisely. Instead, for each new transition t', we only
 * remember the old transitions t that appear either at the very beginning or the very end of some sequence in
 * alpha(t').
 *
 * This class implements a modifiable retromorphism that can be updated to reflect addition or removal of transitions.
 *
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters labeling transitions in the net
 * @param <P>
 *            The type of places
 */
public class ModifiableRetroMorphism<L, P> {

	private final Set<Transition<L, P>> mOriginalTransitions;
	private final HashRelation<Transition<L, P>, Transition<L, P>> mFirstTransitions = new HashRelation<>();
	private final HashRelation<Transition<L, P>, Transition<L, P>> mLastTransitions = new HashRelation<>();

	/**
	 * Creates a new retromorphism; initially the identity.
	 *
	 * @param originalNet
	 *            The original net to which this retromorphism will always map back
	 */
	public ModifiableRetroMorphism(final IPetriNet<L, P> originalNet) {
		mOriginalTransitions = Set.copyOf(originalNet.getTransitions());
	}

	public Set<Transition<L, P>> getFirstTransitions(final Transition<L, P> newTransition) {
		ensureKnown(newTransition);
		if (mOriginalTransitions.contains(newTransition)) {
			return Set.of(newTransition);
		}
		return mFirstTransitions.getImage(newTransition);
	}

	public Set<Transition<L, P>> getLastTransitions(final Transition<L, P> newTransition) {
		ensureKnown(newTransition);
		if (mOriginalTransitions.contains(newTransition)) {
			return Set.of(newTransition);
		}
		return mLastTransitions.getImage(newTransition);
	}

	/**
	 * Update the retromorphism to reflect the addition of a new transition to the net.
	 *
	 * @param transition
	 *            The newly added transition
	 * @param firstTransitions
	 * @param lastTransitions
	 */
	public void addTransition(final Transition<L, P> transition, final Collection<Transition<L, P>> firstTransitions,
			final Collection<Transition<L, P>> lastTransitions) {
		ensureUnknown(transition);
		if (firstTransitions.isEmpty() || lastTransitions.isEmpty()) {
			throw new IllegalArgumentException();
		}

		for (final var first : firstTransitions) {
			ensureKnown(first);
			if (mOriginalTransitions.contains(first)) {
				mFirstTransitions.addPair(transition, first);
			} else {
				copyRelationships(mFirstTransitions, first, transition);
			}
		}

		for (final var last : lastTransitions) {
			ensureKnown(last);
			if (mOriginalTransitions.contains(last)) {
				mLastTransitions.addPair(transition, last);
			} else {
				copyRelationships(mLastTransitions, last, transition);
			}
		}
	}

	/**
	 * Update the retromorphism to reflect that a copy of a transition has been added to the net
	 *
	 * @param transition
	 *            The original transition
	 * @param copy
	 *            The newly added copy
	 */
	public void copyTransition(final Transition<L, P> transition, final Transition<L, P> copy) {
		addTransition(copy, getFirstTransitions(transition), getLastTransitions(transition));
	}

	/**
	 * Update the retromorphism to reflect that a transition has been deleted from the net
	 *
	 * @param transition
	 *            The deleted transition
	 */
	public void deleteTransition(final Transition<L, P> transition) {
		ensureKnown(transition);
		mFirstTransitions.removeDomainElement(transition);
		mLastTransitions.removeDomainElement(transition);
	}

	private void ensureKnown(final Transition<L, P> transition) {
		if (!mOriginalTransitions.contains(transition) && !mFirstTransitions.getDomain().contains(transition)) {
			throw new IllegalArgumentException("Transition " + transition + " is not known");
		}
	}

	private void ensureUnknown(final Transition<L, P> transition) {
		if (mOriginalTransitions.contains(transition) || mFirstTransitions.getDomain().contains(transition)) {
			throw new IllegalArgumentException();
		}
	}

	private static <D, R> void copyRelationships(final HashRelation<D, R> relation, final D from, final D to) {
		relation.addAllPairs(to, relation.getImage(from));
	}
}
