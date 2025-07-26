/*
 * Copyright (C) 2025 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DfgUtils {

	public static <LOC extends IcfgLocation> DfgContainer buildDfg(final IIcfg<LOC> icfg) {
		final Stream<IcfgEdge> edges = IcfgUtils.getAllLocations(icfg).flatMap(x -> x.getOutgoingEdges().stream());
		final Map<IcfgEdge, DfgNode> edgeToNode = edges.collect(Collectors.toMap(x -> x, x -> new DfgNode(x)));

		final Map<LOC, HashRelation<IProgramVar, IcfgEdge>> reachingDefinitions = computeReachingDefinitions(icfg);
		final HashRelation<DfgNode, DfgNode> edgeRelation = new HashRelation<>();

		for (final LOC loc : reachingDefinitions.keySet()) {
			final HashRelation<IProgramVar, IcfgEdge> reach = reachingDefinitions.get(loc);
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				for (final Entry<IProgramVar, HashSet<IcfgEdge>> entry : reach.entrySet()) {
					if (isRead(entry.getKey(), edge.getTransformula())) {
						for (final IcfgEdge def : entry.getValue()) {
							edgeRelation.addPair(edgeToNode.get(def), edgeToNode.get(edge));
						}
					}
				}
			}
		}
		return new DfgContainer(edgeRelation, new HashSet<>(edgeToNode.values()));
	}

	private static <LOC extends IcfgLocation> Map<LOC, HashRelation<IProgramVar, IcfgEdge>>
			computeReachingDefinitions(final IIcfg<LOC> icfg) {

		final Map<LOC, HashRelation<IProgramVar, IcfgEdge>> reachingDefs = new HashMap<>();
		final Map<LOC, Set<IProgramVar>> uninitializedVars = new HashMap<>();
		IcfgUtils.getAllLocations(icfg).forEach(x -> reachingDefs.put(x, new HashRelation<>()));
		IcfgUtils.getAllLocations(icfg).forEach(x -> uninitializedVars.put(x, new HashSet<>()));
		{
			// At the beginning all variables are uninitialized
			for (final LOC loc : icfg.getInitialNodes()) {
				final Set<IProgramVar> uninit = uninitializedVars.get(loc);
				uninit.addAll(icfg.getCfgSmtToolkit().getSymbolTable().getLocals(loc.getProcedure()));
				for (final IProgramNonOldVar pv : icfg.getCfgSmtToolkit().getSymbolTable().getGlobals()) {
					uninit.add(pv);
					uninit.add(pv.getOldVar());
				}
			}
		}
		// TODO: We add elements twice. Use set!
		final ArrayDeque<LOC> worklist = new ArrayDeque<>(icfg.getInitialNodes());
		long iterations = 0;
		while (!worklist.isEmpty()) {
			final LOC src = worklist.removeFirst();
			final HashRelation<IProgramVar, IcfgEdge> srcReachingDefs = reachingDefs.get(src);
			final Set<IProgramVar> srcUninitializedVars = uninitializedVars.get(src);
			for (final IcfgEdge edge : src.getOutgoingEdges()) {
				if (edge instanceof IIcfgInternalTransition) {
					final HashRelation<IProgramVar, IcfgEdge> targetReachingDefs = reachingDefs.get(edge.getTarget());
					final Set<IProgramVar> targetUninitializedVars = uninitializedVars.get(edge.getTarget());
					final boolean wasModified = updateTarget(srcReachingDefs, srcUninitializedVars, edge,
							targetReachingDefs, targetUninitializedVars);

					if (wasModified) {
						worklist.add((LOC) edge.getTarget());
					}

				} else if (edge instanceof IIcfgSummaryTransition) {
					throw new AssertionError();
				} else if (edge instanceof IIcfgCallTransition) {
					throw new AssertionError();
				} else if (edge instanceof IIcfgReturnTransition) {
					throw new AssertionError();
				} else {
					throw new AssertionError("Yet unsupported: " + edge.getClass().getSimpleName());
				}
			}
			iterations++;
		}
		return reachingDefs;
	}

	private static boolean updateTarget(final HashRelation<IProgramVar, IcfgEdge> srcReachingDefs,
			final Set<IProgramVar> srcUninitializedVars, final IcfgEdge edge,
			final HashRelation<IProgramVar, IcfgEdge> targetReachingDefs,
			final Set<IProgramVar> targetUninitializedVars) {
		boolean wasModified = false;
		for (final var pv : srcUninitializedVars) {
			if (isRead(pv, edge.getTransformula())) {
				wasModified |= targetReachingDefs.addPair(pv, edge);
			} else {
				if (isDefAssignment(pv, edge.getTransformula())) {
					// do nothing, the variable gets assigned here
				} else {
					wasModified |= targetUninitializedVars.add(pv);
				}
			}
		}
		for (final IProgramVar pv : srcReachingDefs.getDomain()) {
			if (!isHavoced(pv, edge.getTransformula())) {
				final Set<IcfgEdge> defs = srcReachingDefs.getImage(pv);
				wasModified |= targetReachingDefs.addAllPairs(pv, defs);
			} else {
				wasModified |= targetUninitializedVars.add(pv);
			}
		}
		final Set<IProgramVar> assignedVars = getDefAssignedVars(edge.getTransformula());
		for (final IProgramVar assignedVar : assignedVars) {
			wasModified |= targetReachingDefs.addAllPairs(assignedVar, Set.of(edge));
		}
		return wasModified;
	}

	private static Set<IProgramVar> getDefAssignedVars(final UnmodifiableTransFormula tf) {
		final Set<IProgramVar> result = new HashSet<>();
		for (final IProgramVar pv : tf.getOutVars().keySet()) {
			if (isDefAssignment(pv, tf)) {
				result.add(pv);
			}
		}
		return result;
	}

	private static boolean isDefAssignment(final IProgramVar bv, final UnmodifiableTransFormula tf) {
		final TermVariable inVar = tf.getInVars().get(bv);
		final TermVariable outVar = tf.getOutVars().get(bv);
		if (inVar == outVar) {
			return false;
		}
		return Arrays.asList(tf.getFormula().getFreeVars()).contains(outVar);
	}

	private static boolean isHavoced(final IProgramVar pv, final UnmodifiableTransFormula tf) {
		return tf.isHavocedIn(pv) || tf.isHavocedOut(pv);
	}

	private static boolean isRead(final IProgramVar pv, final UnmodifiableTransFormula tf) {
		final TermVariable inVar = tf.getInVars().get(pv);
		return inVar != null && Arrays.asList(tf.getFormula().getFreeVars()).contains(inVar);
	}

}
