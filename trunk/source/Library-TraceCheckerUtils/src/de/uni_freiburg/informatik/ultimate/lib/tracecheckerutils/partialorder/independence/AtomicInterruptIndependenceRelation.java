/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ISymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation.ISRLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
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
	private final Map<IElement, Boolean> mHasInterruptAnnotation = new HashMap<>();
	private final Map<IElement, InterruptAnnotation> mInterruptAnnotation = new HashMap<>();
	private final Map<String, Set<L>> mProcNameToIsrEntries = new HashMap<>();

	private final IIcfg<?> mIcfg;

	/**
	 * Constructor for an AtomicInterruptIndependenceRelation for the program represented as ICFG and wrt. the
	 * underlying independence relation. The resulting independence relation checks for independence of the whole isr
	 * instead of just the single statement if at least one of the two statements is part of an isr and returns the
	 * independence of underlying in all other cases.
	 *
	 * @param underlying
	 *            Independence relation to be modified wrt. interrupts
	 * @param icfg
	 *            ICFG of the IDP annotated with InterruptAnnotations
	 */
	public AtomicInterruptIndependenceRelation(final IIndependenceRelation<S, L> underlying, final IIcfg<?> icfg) {
		mUnderlying = underlying;
		mIsrDependenceCache = new HashMap<>();
		mIcfg = icfg;
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
		}
		if (isNonISRTransition(a) && isNonISRTransition(b)) {
			return mUnderlying.isIndependent(state, a, b);
		}
		return getInterruptDependence(a, b);
	}

	private boolean fromSameThread(final L a, final L b) {
		return Objects.equals(a.getPrecedingProcedure(), b.getPrecedingProcedure());
	}

	private boolean isNonISRTransition(final L a) {
		return !hasInterruptAnnotation(a);
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
		final ArrayDeque<IIcfgTransition<?>> aTransitionQueue = new ArrayDeque<>(isrAEntryPoints);
		final Set<IIcfgTransition<?>> visitedA = new HashSet<>(isrAEntryPoints);
		while (!aTransitionQueue.isEmpty()) {
			final var currentA = aTransitionQueue.poll();
			addInterruptSuccessorsToQueue(currentA, currentA.getTarget(), aTransitionQueue, visitedA);

			for (final IIcfgTransition<?> currentB : getAllIsrIcfgTransitions(isrBEntryPoints)) {
				if (mUnderlying.isIndependent(null, (L) currentA, (L) currentB) != Dependence.INDEPENDENT) {
					mIsrDependenceCache.put(letterPair, Dependence.DEPENDENT);
					return Dependence.DEPENDENT;
				}
			}
		}
		mIsrDependenceCache.put(letterPair, Dependence.INDEPENDENT);
		return Dependence.INDEPENDENT;
	}

	private Set<IIcfgTransition<?>> getAllIsrIcfgTransitions(final Set<L> entryTransitions) {
		final ArrayDeque<IIcfgTransition<?>> transitionQueue = new ArrayDeque<>(entryTransitions);
		final Set<IIcfgTransition<?>> visited = new HashSet<>(entryTransitions);
		while (!transitionQueue.isEmpty()) {
			final var current = transitionQueue.poll();
			addInterruptSuccessorsToQueue(current, current.getTarget(), transitionQueue, visited);
		}
		return visited;
	}

	private void addInterruptSuccessorsToQueue(final IIcfgTransition<?> currentTransition,
			final IcfgLocation targetNode, final ArrayDeque<IIcfgTransition<?>> transitionQueue,
			final Set<IIcfgTransition<?>> visited) {
		if (!hasInterruptAnnotation(currentTransition) || !hasInterruptAnnotation(targetNode)) {
			return;
		}
		for (final IIcfgTransition<?> icfgEdge : targetNode.getOutgoingEdges()) {
			if (!visited.add(icfgEdge)) {
				continue;
			}
			transitionQueue.offer(icfgEdge);
		}
	}

	@SuppressWarnings("unchecked")
	private Set<L> getIsrEntryTransitions(final L isrTransition) {
		if (!hasInterruptAnnotation(isrTransition)) {
			return Set.of(isrTransition);
		}
		final var isrThreadProcName = isrTransition.getPrecedingProcedure();
		final var cachedIsrEntries = mProcNameToIsrEntries.get(isrThreadProcName);
		if (cachedIsrEntries != null) {
			return cachedIsrEntries;
		}

		assert mIcfg.getProcedureEntryNodes().get(isrThreadProcName) != null;

		final var isrProcEntryEdges = mIcfg.getProcedureEntryNodes().get(isrThreadProcName).getOutgoingEdges();
		final Set<L> isrEntryTransitions = new HashSet<>();
		final ArrayDeque<IIcfgTransition<?>> bfsQueue = new ArrayDeque<>(isrProcEntryEdges);
		final Set<IIcfgTransition<?>> visited =
				Collections.newSetFromMap(new IdentityHashMap<IIcfgTransition<?>, Boolean>());
		visited.addAll(isrProcEntryEdges);
		while (!bfsQueue.isEmpty()) {
			final var currentTransition = bfsQueue.poll();
			final var interruptAnnotation = getInterruptAnnotation(currentTransition);
			final var hasIA = interruptAnnotation != null;
			if (hasIA && interruptAnnotation.getLocation() == ISRLocation.ISR) {
				continue;
			} else if (hasIA && interruptAnnotation.getLocation() == ISRLocation.ENTRY) {
				isrEntryTransitions.add((L) currentTransition);
				continue;
			}

			final var succTransitions = currentTransition.getTarget().getOutgoingEdges();
			for (final IIcfgTransition<?> succTrans : succTransitions) {
				if (visited.add(succTrans)) {
					bfsQueue.offer(succTrans);
				}
			}
		}
		mProcNameToIsrEntries.put(isrThreadProcName, isrEntryTransitions);
		return isrEntryTransitions;
	}

	private boolean hasInterruptAnnotation(final IElement element) {
		return mHasInterruptAnnotation.computeIfAbsent(element,
				e -> mInterruptAnnotation.computeIfAbsent(e, e1 -> InterruptAnnotation.getAnnotation(e1)) != null);
	}

	private InterruptAnnotation getInterruptAnnotation(final IElement element) {
		return mInterruptAnnotation.computeIfAbsent(element, e -> InterruptAnnotation.getAnnotation(e));
	}

	@Override
	public ISymbolicIndependenceRelation<L, S> getSymbolicRelation() {
		throw new UnsupportedOperationException();
	}
}
