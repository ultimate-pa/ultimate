/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayDeque;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;

/**
 * Check given annotation without inferring invariants.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class InvariantChecker {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mToolchainStorage;
	private final IIcfg<IcfgLocation> mIcfg;
	
	private final Map<IcfgLocation, IcfgEdge> mLoopLoc2errorEdge = new HashMap<>();
	private final Map<IcfgLocation, IcfgEdge> mLoopErrorLoc2errorEdge = new HashMap<>();

	public InvariantChecker(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final IIcfg<IcfgLocation> icfg) {
		mServices = services;
		mToolchainStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mIcfg = icfg;
		
		for (final IcfgLocation loopLoc : mIcfg.getLoopLocations()) {
			final IcfgEdge errorEdge = getErrorEdgeForLoopInvariant(loopLoc);
			if (errorEdge == null) {
				throw new UnsupportedOperationException("No invariant at loop " + loopLoc);
			} else {
				mLoopLoc2errorEdge.put(loopLoc, errorEdge);
				mLoopErrorLoc2errorEdge.put(errorEdge.getTarget(), errorEdge);
			}
		}
		
		final Set<IcfgLocation> loopLocsAndNonLoopErrorLocs = new HashSet<>();
		final Map<String, Set<IcfgLocation>> proc2errNodes = icfg.getProcedureErrorNodes();
		for (final Entry<String, Set<IcfgLocation>> entry : proc2errNodes.entrySet()) {
			for (final IcfgLocation errorLoc : entry.getValue()) {
				final IcfgEdge loopErrorEdge = mLoopErrorLoc2errorEdge.get(errorLoc);
				if (loopErrorEdge != null) {
					loopLocsAndNonLoopErrorLocs.add(loopErrorEdge.getSource());
				} else {
					loopLocsAndNonLoopErrorLocs.add(errorLoc);
				}
			}
		}
		
		for (final IcfgLocation backwardStartLoc : loopLocsAndNonLoopErrorLocs) {
			final ArrayDeque<IcfgLocation> worklistBackward = new ArrayDeque<>();
			final Set<IcfgLocation> seenBackward = new HashSet<>();
			final Set<IcfgLocation> startLocations = new HashSet<>();
			worklistBackward.add(backwardStartLoc);
			seenBackward.add(backwardStartLoc);
			while (!worklistBackward.isEmpty()) {
				final IcfgLocation loc = worklistBackward.removeFirst();
				for (final IcfgLocation pred : loc.getIncomingNodes()) {
					if (icfg.getInitialNodes().contains(pred) || icfg.getLoopLocations().contains(pred)) {
						startLocations.add(pred);
					}
					if (!seenBackward.contains(pred)) {
						worklistBackward.add(pred);
						seenBackward.add(pred);
					}
				}
			}
			for (final IcfgLocation startLoc : startLocations) {
				final ArrayDeque<IcfgLocation> worklistForward = new ArrayDeque<>();
				final Set<IcfgEdge> subgraphEdges = new HashSet<>();
				final Set<IcfgLocation> seenForward = new HashSet<>();
				final Set<IcfgLocation> errorLocations = new HashSet<>();
				worklistForward.add(startLoc);
				seenForward.add(startLoc);
				while (!worklistForward.isEmpty()) {
					final IcfgLocation loc = worklistForward.removeFirst();
					for (final IcfgEdge edge : loc.getOutgoingEdges()) {
						final IcfgEdge loopErrorEdge = mLoopErrorLoc2errorEdge.get(loc);
						if (loopErrorEdge != null && edge == loopErrorEdge) {
							// this is edge to error loc for invariant
							continue;
						}
						final IcfgLocation succLoc = edge.getTarget();
						if (!seenBackward.contains(succLoc)) {
							// does not belong to search space
							continue;
						}
						subgraphEdges.add(edge);
						if (icfg.getLoopLocations().contains(succLoc)) {
							final IcfgEdge loopErrorEdgeOfSucc = mLoopLoc2errorEdge.get(succLoc);
							if (loopErrorEdgeOfSucc != null) {
								// succ of edge is loop location
								subgraphEdges.add(loopErrorEdgeOfSucc);
								errorLocations.add(loopErrorEdgeOfSucc.getTarget());
								if (!loopErrorEdgeOfSucc.getTarget().getSuccessors().isEmpty()) {
									throw new UnsupportedOperationException("we presume that error locations do not have successors");
								}
							}
							continue;
						}
						
						if (mIcfg.getProcedureErrorNodes().get(succLoc.getProcedure()).contains(succLoc)) {
							// succLoc is other error location
							errorLocations.add(succLoc);
						}
						if (!seenForward.contains(succLoc)) {
							worklistForward.add(succLoc);
							seenForward.add(succLoc);
						}
					}
				}
				assert !errorLocations.isEmpty();
				final AcyclicSubgraphMerger asm = new AcyclicSubgraphMerger(mServices, mIcfg, subgraphEdges, startLoc, mLoopLoc2errorEdge.get(startLoc), errorLocations);
				for (final IcfgLocation errorLoc : errorLocations) {
					final TransFormula tf = asm.getTransFormula(errorLoc);
					Objects.requireNonNull(tf);
					tf.toString();
				}
			}
		}
	}
	
	public static <E extends IIcfgTransition<IcfgLocation>> Set<E> collectAdjacentEdges(final IIcfg<IcfgLocation> icfg,
			final Set<IcfgLocation> locations) {
		final Set<E> result = new HashSet<>();
		for (final IcfgLocation loc : locations) {
			loc.getOutgoingEdges();
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				if (locations.contains(edge.getTarget())) {
					result.add((E) edge);
				}
			}
		}
		return result;
	}

	private void processForward(final ArrayDeque<IcfgLocation> worklistForward, final Set<IcfgLocation> seenForward,
			final Set<IcfgLocation> errorLocations, final IcfgLocation succLoc, final boolean checkForErrorLocs) {
		seenForward.add(succLoc);
		final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(succLoc);
		if (loa != null) {
			final IcfgLocation eLoc = getErrorEdgeForLoopInvariant(succLoc).getTarget();
			seenForward.add(eLoc);
			errorLocations.add(eLoc);
		} else {
			final Check check = Check.getAnnotation(succLoc);
			if (checkForErrorLocs && check != null) {
				seenForward.add(succLoc);
				errorLocations.add(succLoc);
			} else {
				seenForward.add(succLoc);
				worklistForward.add(succLoc);
			}
		}
	}

	private IcfgEdge getErrorEdgeForLoopInvariant(final IcfgLocation loopLoc) {
		IcfgEdge result = null;
		for (final IcfgEdge succEdge : loopLoc.getOutgoingEdges()) {
			final IcfgLocation succLoc = succEdge.getTarget();
			final Check check = Check.getAnnotation(succLoc);
			if (check != null) {
				final EnumSet<Spec> specs = check.getSpec();
//				if (specs.size() == 1) {
					specs.contains(Spec.INVARIANT);
					if (result == null) {
						result = succEdge;
					} else {
						throw new UnsupportedOperationException("several invariants");
					}
//				} else {
//					throw new UnsupportedOperationException("several specs");
//				}
			}
		}
		if (result == null) {
			throw new UnsupportedOperationException("missing invariant error location");
		}
		return result;
	}
	
	

	
}
