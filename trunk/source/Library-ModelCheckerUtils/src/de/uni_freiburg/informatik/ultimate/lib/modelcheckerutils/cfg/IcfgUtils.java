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

import java.util.ArrayDeque;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.DfsBookkeeping;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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
	 * Collect all program points that are predecessors or successors of an {@link IIcfgCallTransition}.
	 */
	public static <LOC extends IcfgLocation> Set<LOC> getCallerAndCalleePoints(final IIcfg<LOC> icfg) {
		return new IcfgEdgeIterator(icfg).asStream().filter(e -> e instanceof IIcfgCallTransition<?>)
				.flatMap(e -> Stream.of((LOC) e.getSource(), (LOC) e.getTarget())).collect(Collectors.toSet());
	}

	/**
	 * Collect all program points that are predecessors of an {@link IIcfgReturnTransition}.
	 */
	public static <LOC extends IcfgLocation> Set<LOC> getReturnPredecessorPoints(final IIcfg<LOC> icfg) {
		return new IcfgEdgeIterator(icfg).asStream().filter(e -> e instanceof IIcfgReturnTransition)
				.map(x -> (LOC) x.getSource()).collect(Collectors.toSet());
	}

	public static boolean isConcurrent(final IIcfg<?> icfg) {
		return !icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().isEmpty();
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

	public static <LOC extends IcfgLocation> Stream<LOC> getAllLocations(final IIcfg<LOC> icfg) {
		return icfg.getProgramPoints().values().stream().flatMap(x -> x.values().stream());
	}

	public static <LOC extends IcfgLocation> int getNumberOfLocations(final IIcfg<LOC> icfg) {
		return (int) getAllLocations(icfg).count();
	}

	/**
	 * Collects all program variables, both globals and local variables of all procedures. For global variables, both
	 * oldvar and non-oldvar are included.
	 */
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

	public static <LOC extends IcfgLocation> boolean areReachableProgramPointsRegistered(final IIcfg<LOC> icfg) {
		final Set<IcfgLocation> reachableProgramPoints = new IcfgEdgeIterator(icfg).asStream().map(x -> x.getTarget())
				.collect(Collectors.toSet());
		reachableProgramPoints.addAll(icfg.getInitialNodes());
		final Set<LOC> registeredProgramPoints = icfg.getProgramPoints().entrySet().stream()
				.flatMap(x -> x.getValue().entrySet().stream()).map(Entry::getValue).collect(Collectors.toSet());
		final Set<IcfgLocation> diff = new HashSet<>(reachableProgramPoints);
		diff.removeAll(registeredProgramPoints);
		if (!diff.isEmpty()) {
			throw new AssertionError("Program points reachable but not registered: " + diff);
		}
		return true;
	}

	public static <LOC extends IcfgLocation> boolean areRegisteredProgramPointsReachable(final IIcfg<LOC> icfg) {
		final Set<IcfgLocation> reachableProgramPoints = new IcfgEdgeIterator(icfg).asStream().map(x -> x.getTarget())
				.collect(Collectors.toSet());
		reachableProgramPoints.addAll(icfg.getInitialNodes());
		final Set<LOC> registeredProgramPoints = icfg.getProgramPoints().entrySet().stream()
				.flatMap(x -> x.getValue().entrySet().stream()).map(Entry::getValue).collect(Collectors.toSet());
		final Set<IcfgLocation> diff = new HashSet<>(registeredProgramPoints);
		diff.removeAll(reachableProgramPoints);
		// ExitNodes are registered even if they are not reachable (the optimization
		// where we omit ExitNodes would require many case distinctions and would only
		// save a few nodes).
		final Set<LOC> exitProgramPoints = icfg.getProcedureExitNodes().entrySet().stream().map(Entry::getValue)
				.collect(Collectors.toSet());
		diff.removeAll(exitProgramPoints);
		if (!diff.isEmpty()) {
			throw new AssertionError("Program points registered but not reachable: " + diff);
		}
		return true;
	}

	/**
	 * Checks an invariant that must hold for {@link IIcfg}s: For every procedure entry node, there must be a
	 * corresponding procedure exit node, and vice versa. This should hold, even if e.g. the exit node is unreachable.
	 */
	public static <LOC extends IcfgLocation> boolean checkMatchingEntryExitNodes(final IIcfg<LOC> icfg) {
		final var entryNodes = icfg.getProcedureEntryNodes();
		final var exitNodes = icfg.getProcedureExitNodes();

		for (final var e : entryNodes.entrySet()) {
			final var proc = e.getKey();
			assert e.getValue() != null : "Entry node for procedure " + proc + " is null";

			final var exit = exitNodes.get(proc);
			if (exit == null) {
				assert false : "No corresponding exit node for entry node with procedure " + proc;
				return false;
			}
		}

		for (final var e : exitNodes.entrySet()) {
			final var proc = e.getKey();
			assert e.getValue() != null : "Exit node for procedure " + proc + " is null";

			final var entry = entryNodes.get(proc);
			if (entry == null) {
				assert false : "No corresponding entry node for exit node with procedure " + proc;
				return false;
			}
		}

		return true;
	}

	/**
	 * @return true iff loc is entry node of some procedure
	 */
	public static <LOC extends IcfgLocation> boolean isEntry(final LOC loc, final IIcfg<LOC> icfg) {
		final var entry = icfg.getProcedureEntryNodes().get(loc.getProcedure());
		return entry.equals(loc);
	}

	/**
	 * @return true iff loc is exit node of some procedure
	 */
	public static <LOC extends IcfgLocation> boolean isExit(final LOC loc, final IIcfg<LOC> icfg) {
		final var exit = icfg.getProcedureExitNodes().get(loc.getProcedure());
		return loc.equals(exit);
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
	 *            Used to prune edges if paths through such edges should not be considered. However, such edges are
	 *            still considered as target edges.
	 * @param getCachedResult
	 *            A function that retrieves a cached reachability result. SAT represents reachability, UNSAT represents
	 *            non-reachability.
	 * @param setCachedResult
	 *            A function that updates the cache.
	 * @return
	 */
	public static boolean canReachCached(final IcfgLocation sourceLoc, final Predicate<IcfgEdge> isTarget,
			final Predicate<IcfgEdge> prune, final Function<IcfgLocation, LBool> getCachedResult,
			final BiConsumer<IcfgLocation, Boolean> setCachedResult) {
		// First check if result is cached.
		final LBool cachedCanReach = getCachedResult.apply(sourceLoc);
		if (cachedCanReach != LBool.UNKNOWN) {
			return cachedCanReach == LBool.SAT;
		}

		// Do a DFS search of the CFG.
		final DfsBookkeeping<IcfgLocation> dfs = new DfsBookkeeping<>();
		final LinkedList<IcfgLocation> worklist = new LinkedList<>();

		worklist.add(sourceLoc);
		LBool canReach = LBool.UNSAT;

		while (!worklist.isEmpty() && canReach != LBool.SAT) {
			final IcfgLocation currentLoc = worklist.getLast();

			// If the result is cached, retrieve it, mark the location as visited, and backtrack.
			final LBool knownCanReach = getCachedResult.apply(currentLoc);
			if (knownCanReach != LBool.UNKNOWN) {
				// Do not replace UNKNOWN by UNSAT, as we must not propagate this unreachability to predecessors.
				canReach = knownCanReach == LBool.SAT || canReach != LBool.UNKNOWN ? knownCanReach : canReach;

				worklist.removeLast();
				dfs.push(currentLoc);
				dfs.backtrack();
				continue;
			}

			// When backtracking, remember the computed result for future queries.
			if (dfs.isVisited(currentLoc)) {
				assert canReach != LBool.SAT : "After reachability confirmed, should be fast-backtracking";
				worklist.removeLast();

				if (dfs.peek() != currentLoc) {
					// Node might have been added to worklist multiple times and since been visited. Hence it might not
					// be on the stack. In that case, no backtracking is needed, nor do we visit the node again.
					continue;
				}

				final boolean completeBacktrack = dfs.backtrack();
				// Inside a loop, reachability cannot be UNSAT. Yet, a successor outside the loop might have
				// UNSAT status. Once back inside the loop, we here set canReach to UNKNOWN.
				// Conversely, if we just backtracked the outermost loop head, reset canReach to UNSAT.
				canReach = completeBacktrack ? LBool.UNSAT : LBool.UNKNOWN;

				if (canReach != LBool.UNKNOWN) {
					assert canReach == LBool.UNSAT;
					setCachedResult.accept(currentLoc, false);
				}
				continue;
			}

			// Visit location.
			dfs.push(currentLoc);

			final List<IcfgEdge> outgoing = currentLoc.getOutgoingEdges();
			final List<IcfgLocation> successors = new ArrayList<>(outgoing.size());
			for (final IcfgEdge edge : outgoing) {
				final IcfgLocation succ = edge.getTarget();

				// Abort when reachability is confirmed.
				if (isTarget.test(edge)) {
					canReach = LBool.SAT;
					break;
				}

				// Ignore successors of explicitly pruned edges.
				if (prune.test(edge)) {
					continue;
				}

				final int stackIndex;
				if (!dfs.isVisited(succ)) {
					// If the successor has not been visited before, explore it now.
					successors.add(succ);
				} else if ((stackIndex = dfs.stackIndexOf(succ)) != -1) {
					// If the edge leads back to the stack, reachability is unknown until succ (or an even earlier loop
					// head) is backtracked. To avoid infinite looping, we do not explore succ.
					assert getCachedResult
							.apply(succ) == LBool.UNKNOWN : "Loop heads on stack must have UNKNOWN status";
					canReach = LBool.UNKNOWN;
					dfs.updateLoopHead(currentLoc, new Pair<>(stackIndex, succ));
				} else {
					// If the successor has been visited before, but is not on the stack, then we know its reachability
					// is either UNSAT or UNKNOWN.
					final LBool succCanReach = getCachedResult.apply(succ);
					assert succCanReach != LBool.SAT : "Backtracked node must not have SAT status";

					// In either case, we do not need to explore it again. Instead, we simply propagate reachability and
					// loop head information back to currentLoc.
					canReach = succCanReach == LBool.UNKNOWN ? LBool.UNKNOWN : canReach;
					dfs.backPropagateLoopHead(currentLoc, succ);
				}
			}

			// When reachability was confirmed, do not search any further.
			if (canReach != LBool.SAT) {
				successors.stream().forEach(worklist::add);
			}
		}

		// Fast-backtrack: If we exited the previous loop because reachability was confirmed,
		// we only backtrack, and no longer explore states on the work list.
		while (!dfs.isStackEmpty()) {
			assert canReach == LBool.SAT : "Fast-backtracking must only happen in case of reachability";
			final IcfgLocation currentLoc = dfs.peek();
			dfs.backtrack();
			setCachedResult.accept(currentLoc, true);
		}

		final LBool cachedReachability = getCachedResult.apply(sourceLoc);
		assert cachedReachability != LBool.UNKNOWN : "reachability should be clearly determined";
		assert cachedReachability == canReach : "contradictory reachability: " + cachedReachability + " != " + canReach;
		return canReach == LBool.SAT;
	}

	public static <LOC extends IcfgLocation> Set<String> getAllThreadInstances(final IIcfg<LOC> icfg) {
		final Stream<String> threadInstances =
				icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().values().stream()
						.flatMap(Collection::stream).map(ThreadInstance::getThreadInstanceName);
		final String mainThread =
				DataStructureUtils.getOneAndOnly(icfg.getInitialNodes(), "initial node").getProcedure();
		return Stream.concat(Stream.of(mainThread), threadInstances).collect(Collectors.toSet());
	}

	public static Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> getForksInLoop(final IIcfg<?> icfg) {
		final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> result = new HashSet<>();
		final Map<String, ? extends IcfgLocation> entryLocs = icfg.getProcedureEntryNodes();
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			final ArrayDeque<IcfgLocation> queue = new ArrayDeque<>();
			final Set<IcfgLocation> visited = new HashSet<>();
			queue.add(fork.getTarget());
			queue.add(entryLocs.get(fork.getNameOfForkedProcedure()));
			while (!queue.isEmpty()) {
				final IcfgLocation loc = queue.pop();
				if (!visited.add(loc)) {
					continue;
				}
				if (loc.equals(fork.getSource())) {
					result.add(fork);
					break;
				}
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					queue.add(edge.getTarget());
					if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
						final var fork2 = (IIcfgForkTransitionThreadCurrent<?>) edge;
						queue.add(entryLocs.get(fork2.getNameOfForkedProcedure()));
					}
				}
			}
		}
		return result;
	}
}
