package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ISymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Independence class for interrupt-driven programs where an interrupt consisting of possibly multiple statements gets
 * executed atomically. Checks independence for interrupt and non-interrupt transitions in a way, that they only
 * commute, if the whole interrupt commutes with the non-interrupt transition. If both transitions are not part of any
 * ISR, the underlying independence is applied.
 *
 * @param <S>
 *            The type of states of the underlying automaton
 * @param <L>
 *            The type of transitions of the underlying automaton
 */
public class AtomicInterruptIndependenceRelation<S, L extends IIcfgTransition<?>>
		implements IIndependenceRelation<S, L> {
	private final IIndependenceRelation<S, L> mUnderlying;
	// Store the dependences for pairs where at least one is part of an ISR
	private final Map<Pair<Set<L>, Set<L>>, Dependence> mIsrDependenceCache;

	private final ILogger mLogger;

	public AtomicInterruptIndependenceRelation(final IIndependenceRelation<S, L> underlying, final ILogger logger) {
		mUnderlying = underlying;
		mIsrDependenceCache = new HashMap<>();
		mLogger = logger;
	}

	@Override
	public boolean isSymmetric() {
		// TODO: Should it be symmetric?
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		// TODO: Ensure that the Independence relation is always unconditional
		return false;
	}

	@Override
	public Dependence isIndependent(final S state, final L a, final L b) {
		if (fromSameThread(a, b)) {
			return Dependence.DEPENDENT;
		} else if (isNonISRTransition(a) && isNonISRTransition(b)) {
			if (isIsrPredecessor(a) || isIsrPredecessor(b)) {
				return Dependence.DEPENDENT;
			}
			return mUnderlying.isIndependent(null, a, b);
		}
		return getInterruptDependence(a, b);
	}

	private boolean isIsrPredecessor(final L transition) {
		final var succTransitions = transition.getTarget().getOutgoingEdges();
		return !succTransitions.stream().anyMatch(e -> InterruptAnnotations.hasAnnotation(e));
	}

	private boolean isNonISRTransition(final L a) {
		return !InterruptAnnotations.hasAnnotation(a);
	}

	@SuppressWarnings("unchecked")
	private Dependence getInterruptDependence(final L a, final L b) {
		final var isrAEntryPoints = getIsrEntryTransitions(a);
		final var isrBEntryPoints = getIsrEntryTransitions(b);
		final var letterPair = new Pair<>(isrAEntryPoints, isrBEntryPoints);
		final var cachedDependence = mIsrDependenceCache.get(letterPair);
		if (cachedDependence != null) {
			return cachedDependence;
		}

		// Store transition a in queue for BFS
		final HashDeque<IIcfgTransition<?>> aTransitionQueue = new HashDeque<>();
		for (final L aEntry : isrAEntryPoints) {
			aTransitionQueue.offer(aEntry);
		}
		while (!aTransitionQueue.isEmpty()) {
			final var currentA = aTransitionQueue.poll();
			final var aTargetNode = currentA.getTarget();
			if (InterruptAnnotations.hasAnnotation(currentA) && InterruptAnnotations.hasAnnotation(aTargetNode)) {
				final var successors = aTargetNode.getOutgoingEdges();
				for (final IIcfgTransition<?> icfgEdge : successors) {
					aTransitionQueue.offer(icfgEdge);
				}
			}
			// Store transition b in queue for BFS
			final HashDeque<IIcfgTransition<?>> bTransitionQueue = new HashDeque<>();
			for (final L bEntry : isrBEntryPoints) {
				bTransitionQueue.offer(bEntry);
			}
			while (!bTransitionQueue.isEmpty()) {
				final var currentB = bTransitionQueue.poll();
				final var bTargetNode = currentB.getTarget();
				if (InterruptAnnotations.hasAnnotation(currentB) && InterruptAnnotations.hasAnnotation(bTargetNode)) {
					final var successors = bTargetNode.getOutgoingEdges();
					for (final IIcfgTransition<?> icfgEdge : successors) {
						bTransitionQueue.offer(icfgEdge);
					}
				}
				if (mUnderlying.isIndependent(null, (L) currentA, (L) currentB) != Dependence.INDEPENDENT) {
					mIsrDependenceCache.put(letterPair, Dependence.DEPENDENT);
					return Dependence.DEPENDENT;
				}
			}
		}
		mIsrDependenceCache.put(letterPair, Dependence.INDEPENDENT);
		return Dependence.INDEPENDENT;
	}

	@SuppressWarnings("unchecked")
	private Set<L> getIsrEntryTransitions(final L isrTransition) {
		if (!InterruptAnnotations.hasAnnotation(isrTransition)) {
			return Set.of(isrTransition);
		}
		final Set<L> isrEntryTransition = new HashSet<>();
		final HashDeque<L> bfsQueue = new HashDeque<>();
		bfsQueue.add(isrTransition);
		while (!bfsQueue.isEmpty()) {
			final var currentTransition = bfsQueue.poll();
			final var predNode = currentTransition.getSource();
			final var predTransitions = predNode.getIncomingEdges();
			final var predIsrTransitions =
					predTransitions.stream().filter(t -> InterruptAnnotations.hasAnnotation(t)).toList();
			if (predIsrTransitions.isEmpty()) {
				isrEntryTransition.add(currentTransition);
				continue;
			}
			for (final IIcfgTransition<?> icfgEdge : predIsrTransitions) {
				bfsQueue.offer((L) icfgEdge);
			}
		}
		return isrEntryTransition;
	}

	private boolean fromSameThread(final L a, final L b) {
		// TODO: Duplicated method from ThreadSeperatingIndependence. Maybe we can ensure that underlying is already
		// thread-separating?
		return Objects.equals(a.getPrecedingProcedure(), b.getPrecedingProcedure());
	}

	@Override
	public ISymbolicIndependenceRelation<L, S> getSymbolicRelation() {
		throw new UnsupportedOperationException();
	}
}
