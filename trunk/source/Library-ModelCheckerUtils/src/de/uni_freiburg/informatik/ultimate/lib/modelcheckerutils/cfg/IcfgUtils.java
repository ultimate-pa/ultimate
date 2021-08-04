/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgUtils {

	private IcfgUtils() {
		// do not instantiate utility class
	}

	public static <LOC extends IcfgLocation> Set<LOC> getPotentialCycleProgramPoints(final IIcfg<LOC> icfg) {
		return new IcfgLocationIterator<>(icfg).asStream().filter(a -> a.getOutgoingEdges().stream().anyMatch(b -> {
			final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(b);
			return loa != null && loa.getLoopEntryType() == LoopEntryType.GOTO;
		})).collect(Collectors.toSet());
	}

	/**
	 * @return {@link List} that contains all {@link IcfgEdge}s that originate from an initial location.
	 */
	public static <LOC extends IcfgLocation> List<IcfgEdge> extractStartEdges(final IIcfg<LOC> icfg) {
		return icfg.getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream()).collect(Collectors.toList());
	}

	public static <T extends IIcfgTransition<?>> UnmodifiableTransFormula getTransformula(final T transition) {
		if (transition instanceof IInternalAction) {
			return ((IInternalAction) transition).getTransformula();
		}
		if (transition instanceof ICallAction) {
			return ((ICallAction) transition).getLocalVarsAssignment();
		}
		if (transition instanceof IReturnAction) {
			return ((IReturnAction) transition).getAssignmentOfReturn();
		} else {
			throw new UnsupportedOperationException(
					"Dont know how to extract transformula from transition " + transition);
		}
	}

	public static <LOC extends IcfgLocation> Set<LOC> getErrorLocations(final IIcfg<LOC> icfg) {
		final Set<LOC> errorLocs = new LinkedHashSet<>();
		for (final Entry<String, Set<LOC>> entry : icfg.getProcedureErrorNodes().entrySet()) {
			errorLocs.addAll(entry.getValue());
		}
		return errorLocs;
	}

	public static <LOC extends IcfgLocation> boolean isErrorLocation(final IIcfg<LOC> icfg, final IcfgLocation loc) {
		if (icfg == null) {
			throw new IllegalArgumentException();
		}
		if (loc == null) {
			return false;
		}

		final String proc = loc.getProcedure();
		final Map<String, Set<LOC>> errorNodes = icfg.getProcedureErrorNodes();
		if (errorNodes == null || errorNodes.isEmpty()) {
			return false;
		}
		final Set<LOC> procErrorNodes = errorNodes.get(proc);
		if (procErrorNodes == null || procErrorNodes.isEmpty()) {
			return false;
		}
		return procErrorNodes.contains(loc);
	}

	public static <LOC extends IcfgLocation> int getNumberOfLocations(final IIcfg<LOC> icfg) {
		int result = 0;
		for (final Entry<String, Map<DebugIdentifier, LOC>> entry : icfg.getProgramPoints().entrySet()) {
			result += entry.getValue().size();
		}
		return result;
	}

	public static Set<IProgramVar> collectAllProgramVars(final CfgSmtToolkit csToolkit) {
		final Set<IProgramVar> result = new HashSet<>();
		for (final IProgramNonOldVar nonold : csToolkit.getSymbolTable().getGlobals()) {
			result.add(nonold);
			final IProgramOldVar oldVar = nonold.getOldVar();
			result.add(oldVar);
		}
		for (final String proc : csToolkit.getProcedures()) {
			result.addAll(csToolkit.getSymbolTable().getLocals(proc));
		}
		return result;
	}

	/**
	 * Compute a hashcode for the graph structure of an ICFG. The hashcode is is only based on the hashcode of locations
	 * and edges and ignores {@link IProgramVar}s and other objects that come along with an ICFG. The method can help
	 * while debugging in order to find nondeterminism in our implementation.
	 */
	public static <LOC extends IcfgLocation> int computeIcfgHashCode(final IIcfg<LOC> icfg) {
		final IcfgLocationIterator<LOC> locIt = new IcfgLocationIterator<>(icfg);
		int result = 0;
		while (locIt.hasNext()) {
			final LOC loc = locIt.next();
			result += loc.hashCode();
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				result += edge.hashCode();
			}
		}
		return result;
	}

	public static <LOC extends IcfgLocation> boolean hasUnreachableProgramPoints(final IIcfg<LOC> icfg) {
		for (final Entry<String, Map<DebugIdentifier, LOC>> entry : icfg.getProgramPoints().entrySet()) {
			for (final Entry<DebugIdentifier, LOC> innerEntry : entry.getValue().entrySet()) {
				final LOC loc = innerEntry.getValue();
				if (loc.getIncomingEdges().isEmpty() && !isEntry(loc, icfg) && !isExit(loc, icfg)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * @return true iff loc is entry node of some procedure
	 */
	public static <LOC extends IcfgLocation> boolean isEntry(final LOC loc, final IIcfg<LOC> icfg) {
		return icfg.getProcedureEntryNodes().get(loc.getProcedure()).equals(loc);
	}

	/**
	 * @return true iff loc is exit node of some procedure
	 */
	public static <LOC extends IcfgLocation> boolean isExit(final LOC loc, final IIcfg<LOC> icfg) {
		return icfg.getProcedureExitNodes().get(loc.getProcedure()).equals(loc);
	}

	/**
	 * Determines if a given edge is currently enabled, given the set of current locations (across all thread instances)
	 *
	 * Note that {@link IIcfgForkTransitionThreadCurrent} and {@link IIcfgJoinTransitionThreadCurrent} are never
	 * considered enabled, but their counterparts ({@link IIcfgForkTransitionThreadOther} and
	 * {@link IIcfgJoinTransitionThreadOther}) are.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <LOC>
	 *            The type of locations
	 * @param locs
	 *            The set of all current locations
	 * @param edge
	 *            An edge of the CFG
	 * @return true iff the given edge is enabled
	 */
	public static <LOC extends IcfgLocation> boolean isEnabled(final Set<LOC> locs, final IcfgEdge edge) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>
				|| edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
			// These edges exist in the Icfg, but in traces they are represented by the respective
			// IIcfg*TransitionThreadOther transitions. Hence they are never enabled.
			return false;
		}
		if (edge instanceof IIcfgForkTransitionThreadOther<?>) {
			// Enabled if predecessor location is in state, and forked thread instance is not yet running.
			final Set<String> threads = locs.stream().map(IcfgLocation::getProcedure).collect(Collectors.toSet());
			final String forkedThread = edge.getSucceedingProcedure();
			return locs.contains(edge.getSource()) && !threads.contains(forkedThread);
		}
		if (edge instanceof IIcfgJoinTransitionThreadOther<?>) {
			// Enabled if predecessor location and predecessor location of the corresponding
			// IIcfg*TransitionThreadCurrent instance are both in the state.
			final var joinOther = (IIcfgJoinTransitionThreadOther<?>) edge;
			final var joinCurrent = joinOther.getCorrespondingIIcfgJoinTransitionCurrentThread();
			return locs.contains(joinOther.getSource()) && locs.contains(joinCurrent.getSource());
		}
		return locs.contains(edge.getSource());
	}

	/**
	 * Performs a DFS to determine if from a given source location, a target edge can be reached. A given cache allows
	 * re-using results across queries.
	 *
	 * @param sourceLoc
	 *            The source location from which reachability is checked.
	 * @param isTarget
	 *            Identifies target edges.
	 * @param prune
	 *            Used to prune edges if paths though such an edges should not be considered.
	 * @param getCachedResult
	 *            A function that retrieves a cached reachability result. UNSAT represents reachability, SAT represents
	 *            non-reachability.
	 * @param setCachedResult
	 *            A function that updates the cache.
	 * @return
	 */
	public static boolean canReachCached(final IcfgLocation sourceLoc, final Predicate<IcfgEdge> isTarget,
			final Predicate<IcfgEdge> prune, final Function<IcfgLocation, LBool> getCachedResult,
			final BiConsumer<IcfgLocation, Boolean> setCachedResult) {
		final LBool REACHABLE = LBool.UNSAT;
		final LBool UNREACHABLE = LBool.SAT;
		final LBool UNKNOWN = LBool.UNKNOWN;

		// First check if result is cached.
		final LBool cachedCanReach = getCachedResult.apply(sourceLoc);
		if (cachedCanReach != UNKNOWN) {
			return cachedCanReach == REACHABLE;
		}

		// Do a DFS search of the CFG.
		final Set<IcfgLocation> visited = new HashSet<>();
		final LinkedList<IcfgLocation> worklist = new LinkedList<>();
		worklist.add(sourceLoc);

		LBool canReach = UNREACHABLE;
		int loopHeadIndex = -1;
		IcfgLocation loopHead = null;

		while (!worklist.isEmpty() && canReach != REACHABLE) {
			assert loopHeadIndex == -1 || canReach != UNREACHABLE : "Inside a loop unreachability cannot be confirmed";
			assert loopHeadIndex != -1 || canReach != UNKNOWN : "Reachability should be known unless in a loop";
			assert (loopHeadIndex < 0) == (loopHead == null) : "Inconsistent loop head tracking";
			assert loopHeadIndex < 0 || worklist.get(loopHeadIndex) == loopHead : "Inconsistent loop head tracking";

			final IcfgLocation currentLoc = worklist.getLast();

			// If the result is cached, retrieve it, mark the location as visited, and start backtracking.
			final LBool knownCanReach = getCachedResult.apply(currentLoc);
			if (knownCanReach != UNKNOWN) {
				// Do not replace UNKNOWN by UNREACHABLE, as we must not propagate this unreachability to predecessors.
				canReach = knownCanReach == REACHABLE || canReach != UNKNOWN ? knownCanReach : canReach;
				visited.add(currentLoc);
			}

			// When backtracking, remember the computed result for future queries.
			if (visited.contains(currentLoc)) {
				worklist.removeLast();
				// When backtracking the outermost encountered loop head, reachability must be either REACHABLE or
				// UNKNOWN. In the latter case, we can now set it to UNREACHABLE.
				// TODO Theoretically, we could even store UNREACHABLE for all nodes reached from the loop head.
				if (loopHeadIndex == worklist.size()) {
					assert canReach != UNREACHABLE : "Can not determine unreachability within loop";
					assert loopHead == currentLoc : "Unexpected loop head: expected " + loopHead + ", got "
							+ currentLoc;
					loopHeadIndex = -1;
					loopHead = null;
					canReach = canReach == UNKNOWN ? UNREACHABLE : canReach;
				}
				if (canReach != UNKNOWN) {
					setCachedResult.accept(currentLoc, canReach == REACHABLE);
				}
				continue;
			}

			// Mark location as visited.
			visited.add(currentLoc);

			final List<IcfgEdge> outgoing = currentLoc.getOutgoingEdges();
			final List<IcfgLocation> successors = new ArrayList<>(outgoing.size());
			for (final IcfgEdge edge : outgoing) {
				final IcfgLocation succ = edge.getTarget();

				// Ignore explicitly pruned edges.
				if (prune.test(edge)) {
					continue;
				}

				// Abort when reachability is confirmed.
				if (isTarget.test(edge)) {
					canReach = REACHABLE;
					break;
				}

				final boolean succVisited = visited.contains(succ);
				final int stackIndex;
				if (succVisited && (stackIndex = worklist.indexOf(succ)) != -1) {
					// If the edge leads back to the stack, reachability is unknown until succ (or an even earlier loop
					// head) is backtracked. To avoid infinite looping, we do not explore succ.
					assert getCachedResult.apply(succ) == UNKNOWN;
					canReach = UNKNOWN;
					loopHeadIndex = loopHeadIndex < 0 ? stackIndex : Integer.min(loopHeadIndex, stackIndex);
					loopHead = loopHeadIndex == stackIndex ? succ : loopHead;
				} else if (succVisited) {
					// If the successor has been visited before, but is not on the stack, then we know its reachability
					// is either UNREACHABLE or UNKNOWN. In either case, we do not need to explore it again.
					assert getCachedResult.apply(succ) != REACHABLE;
				} else {
					// If the successor has not been visited before, explore it now.
					successors.add(succ);
				}
			}

			// When reachability was confirmed, do not search any further.
			if (canReach != REACHABLE) {
				successors.stream().forEach(worklist::add);
			}
		}

		// Fast-backtrack: If we exited the previous loop because reachability was confirmed,
		// we only backtrack, and no longer explore states on the work list.
		while (!worklist.isEmpty()) {
			assert canReach == REACHABLE : "Fast-backtracking must only happen in case of reachability";
			final IcfgLocation currentLoc = worklist.removeLast();
			if (visited.contains(currentLoc)) {
				// If a state on the worklist is marked as visited, it is on the stack.
				// Hence mark it as being able to reach the target.
				setCachedResult.accept(currentLoc, true);
			}
		}

		final LBool computedReachability = getCachedResult.apply(sourceLoc);
		assert computedReachability != UNKNOWN : "Reachability should be clearly determined";
		assert computedReachability == canReach : "Incoherent reachability result";
		return canReach == REACHABLE;
	}

	public static <LOC extends IcfgLocation> Set<String> getAllThreadInstances(final IIcfg<LOC> icfg) {
		final Stream<String> threadInstances =
				icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().values().stream()
						.flatMap(Collection::stream).map(ThreadInstance::getThreadInstanceName);
		final String mainThread =
				DataStructureUtils.getOneAndOnly(icfg.getInitialNodes(), "initial node").getProcedure();
		return Stream.concat(Stream.of(mainThread), threadInstances).collect(Collectors.toSet());
	}
}
