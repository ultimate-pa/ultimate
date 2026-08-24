/*
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-srParse plug-in.
 *
 * The ULTIMATE Library-srParse plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-srParse plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-srParse plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-srParse plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-srParse plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.BoundTypes;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

public abstract class AutomatonPatternType<T extends AutomatonPatternType<?>> extends PatternType<T> {

	public AutomatonPatternType(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		super(scope, id, cdds, durations, durationNames);
	}

	public CDD getSourceLocation() {
		final List<CDD> cdds = getCdds();
		return cdds.get(cdds.size() - 1);
	}

	public CDD getTargetLocation() {
		final List<CDD> cdds = getCdds();
		return cdds.get(cdds.size() - 2);
	}

	public CDD getGuard() {
		return CDD.TRUE;
	}

	public CDD getEvent() {
		return CDD.TRUE;
	}

	public BoundTypes getBoundType() {
		return BoundTypes.NONE;
	}

	public int getBoundValue() {
		return 0;
	}

	public boolean isInitialLocation() {
		return false;
	}

	@Override
	protected final List<CounterTrace> transform(final CDD[] cdds, final int[] durations,
			final List<PatternType<?>> allPatterns, final ILogger logger) {
		if (!(getScope() instanceof SrParseScopeGlobally)) {
			throw new PatternScopeNotImplemented(getScope().getClass(), getClass());
		}
		return buildCounterTraces(allPatterns, logger);
	}

	protected List<CounterTrace> buildCounterTraces(final List<PatternType<?>> allPatterns, final ILogger logger) {
		final List<CounterTrace> result = new ArrayList<>();

		if (isInitialLocation()) {
			result.add(buildInitialCounterTrace(allPatterns, logger));
		} else {
			final List<AutomatonPatternType<?>> outgoingTransitions =
					getAllOutgoingEdges(allPatterns, getSourceLocation());
			result.add(buildEventLocked(outgoingTransitions));
			if (getEvent() != CDD.TRUE) {
				result.add(buildEventArmed(outgoingTransitions));
			}
			if (getBoundType() != BoundTypes.NONE) {
				result.add(buildTimeBound(outgoingTransitions));
			}

		}

		// TODO check if target location of transition has outgoing edges. If not add t;l;!l;t to counter traces

		return result;
	}

	private static List<AutomatonPatternType<?>> getAllOutgoingEdges(final List<PatternType<?>> allPatterns,
			final CDD sourceLoc) {
		return allPatterns.stream().filter(p -> p instanceof AutomatonPatternType<?>)
				.map(p -> (AutomatonPatternType<?>) p)
				.filter(p -> !p.isInitialLocation() && cddAreEquivalent(p.getSourceLocation(), sourceLoc))
				.collect(Collectors.toList());
	}

	/**
	 * Returns all automaton patterns that belong to the same automaton as this pattern.
	 */
	protected List<AutomatonPatternType<?>> getHull(final List<PatternType<?>> allPatterns, final ILogger logger) {
		final List<AutomatonPatternType<?>> allAutomaton =
				allPatterns.stream().filter(p -> p instanceof AutomatonPatternType<?>)
						.map(p -> (AutomatonPatternType<?>) p).collect(Collectors.toList());

		final Set<AutomatonPatternType<?>> hull = new LinkedHashSet<>();
		final Queue<AutomatonPatternType<?>> queue = new ArrayDeque<>();
		hull.add(this);
		queue.add(this);

		while (!queue.isEmpty()) {
			final AutomatonPatternType<?> pivot = queue.poll();
			final CDD pivotTarget = pivot.getTargetLocation();
			final CDD pivotSource = pivot.getSourceLocation();
			for (final AutomatonPatternType<?> p : allAutomaton) {
				if (p.isInitialLocation() || hull.contains(p)) {
					continue;
				}
				if (cddAreEquivalent(p.getSourceLocation(), pivotTarget)
						|| cddAreEquivalent(p.getTargetLocation(), pivotTarget)
						|| cddAreEquivalent(p.getSourceLocation(), pivotSource)
						|| cddAreEquivalent(p.getTargetLocation(), pivotSource)) {
					hull.add(p);
					queue.add(p);
				}
			}
		}

		// Collect all locations present in the hull
		final Set<CDD> hullLocations = new LinkedHashSet<>();
		for (final AutomatonPatternType<?> p : hull) {
			hullLocations.add(p.getSourceLocation());
			hullLocations.add(p.getTargetLocation());
		}

		// Pull in InitialLocPatterns that reference any hull location
		for (final AutomatonPatternType<?> p : allAutomaton) {
			if (!p.isInitialLocation()) {
				continue;
			}
			final CDD initLoc = p.getTargetLocation();
			for (final CDD loc : hullLocations) {
				if (cddAreEquivalent(initLoc, loc)) {
					hull.add(p);
					break;
				}
			}
		}

		return new ArrayList<>(hull);
	}

	private static boolean cddAreEquivalent(final CDD a, final CDD b) {
		return a.isEqual(b); // TODO use an SMT solver to check semantic equivalence instead of syntactic
	}

	private CounterTrace buildInitialCounterTrace(final List<PatternType<?>> allPatterns, final ILogger logger) {
		final List<AutomatonPatternType<?>> hull = getHull(allPatterns, logger);

		CDD allInitials = CDD.FALSE;
		for (final AutomatonPatternType<?> p : hull) {
			if (p.isInitialLocation()) {
				allInitials = allInitials.or(p.getSourceLocation());
			}
		}

		return counterTrace(phase(allInitials.negate()), phaseT());
	}

	/**
	 * Formula 17: event is set from entry (event is true and stays true)
	 */
	private CounterTrace buildEventLocked(final List<AutomatonPatternType<?>> outgoingTransitions) {
		CDD otherTransitions = CDD.FALSE;

		for (final AutomatonPatternType<?> transition : outgoingTransitions) {
			if (transition.getEvent() != CDD.TRUE && transition.getEvent() == getEvent()) {
				continue;
			}
			otherTransitions = otherTransitions
					.or(transition.getTargetLocation().and(transition.getGuard()).and(transition.getEvent()));
		}

		final CDD secondPhase = getSourceLocation().and(getEvent());
		final CDD thirdPhase = getSourceLocation().or(otherTransitions).negate();
		return counterTrace(phaseT(), phase(secondPhase), phase(thirdPhase), phaseT());
	}

	/**
	 * Formula 18: event is not set (and may trigger a transition)
	 */
	private CounterTrace buildEventArmed(final List<AutomatonPatternType<?>> outgoingTransitions) {
		CDD otherTransitions = CDD.FALSE;

		for (final AutomatonPatternType<?> transition : outgoingTransitions) {
			otherTransitions = otherTransitions
					.or(transition.getTargetLocation().and(transition.getGuard()).and(transition.getEvent()));
		}

		final CDD secondPhase = getSourceLocation().and(getEvent().negate());
		final CDD thirdPhase = secondPhase.or(otherTransitions).negate();
		return counterTrace(phaseT(), phase(secondPhase), phase(thirdPhase), phaseT());
	}

	/**
	 * Formula 20: time bounds in locations
	 */
	protected CounterTrace buildTimeBound(final List<AutomatonPatternType<?>> outgoingTransitions) {
		CDD otherTransitions = CDD.FALSE;

		for (final AutomatonPatternType<?> transition : outgoingTransitions) {
			if (transition.getEvent() != CDD.TRUE && transition.getEvent() == getEvent()) {
				continue;
			}
			otherTransitions = otherTransitions
					.or(transition.getTargetLocation().and(transition.getGuard()).and(transition.getEvent()));
		}

		// TODO TK hier bin ich mir nicht mehr sicher
		final CDD thirdPhase = getTargetLocation().and(getEvent()).and(getGuard()).and(otherTransitions.negate());
		return counterTrace(phaseT(), phase(getSourceLocation(), invertBound(getBoundType()), getBoundValue()),
				phase(thirdPhase), phaseT());
	}

	private static BoundTypes invertBound(final BoundTypes boundType) {
		switch (boundType) {
		case GREATEREQUAL:
			return BoundTypes.LESS;
		case LESSEQUAL:
			return BoundTypes.GREATER;
		case GREATER:
			return BoundTypes.LESSEQUAL;
		case LESS:
			return BoundTypes.GREATEREQUAL;
		default:
			return BoundTypes.NONE;
		}
	}
}
