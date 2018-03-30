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

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Merge an acyclic subgraph into a list of {@link UnmodifiableTransFormula}s.
 * Given 
 * <ul>
 *  <li> an ICFG mICFG,
 *  <li> a set of {@link IcfgEdge}s that defines an acyclic and connected 
 *  subgraph of mICFG,
 *  <li> a location startLoc such that all edges of the subgraph are successors
 *  of startLoc,
 *  <li> and a a set of locations {endLoc_1, ..., endloc L_n},
 * </ul> 
 * construct {@link UnmodifiableTransFormula}s tf_1,...tf_n such that
 * tf_i represents the disjunction of all paths from startLoc to endLoc_i.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class AcyclicSubgraphMerger {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<IcfgLocation> mIcfg;
	private final Set<IcfgLocation> mSubgraph;
	private final Set<IcfgEdge> mSubgraphEdges;
	private final IcfgLocation mSubgraphStartLocation;
	private final IcfgLocation mSubgraphEndLocations;
	
	private final Map<IcfgLocation, UnmodifiableTransFormula> mEndloc2TransFormula;

	
	
	
	public AcyclicSubgraphMerger(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final Set<IcfgLocation> subgraph, final Set<IcfgEdge> subgraphEdges, final IcfgLocation subgraphStartLocation,
			final IcfgLocation subgraphEndLocations) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mIcfg = icfg;
		mSubgraph = subgraph;
		mSubgraphEdges = subgraphEdges;
		mSubgraphStartLocation = subgraphStartLocation;
		mSubgraphEndLocations = subgraphEndLocations;
		mEndloc2TransFormula = null;
	}
	
	/**
	 * @return {@link UnmodifiableTransFormula} that represents the disjunction 
	 * of all paths from startLoc to endLoc.
	 */
	public UnmodifiableTransFormula getTransFormula(final IcfgLocation endLoc) {
		return mEndloc2TransFormula.get(endLoc);
	}
	
	

//	public AcyclicSubgraphMerger(final IUltimateServiceProvider services, final IToolchainStorage storage,
//			final IIcfg<IcfgLocation> icfg) {
//		mServices = services;
//		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
//		mIcfg = icfg;
//		final Map<String, Set<IcfgLocation>> proc2errNodes = icfg.getProcedureErrorNodes();
//		for (final Entry<String, Set<IcfgLocation>> entry : proc2errNodes.entrySet()) {
//			for (final IcfgLocation errorLoc : entry.getValue()) {
//				
//				final ArrayDeque<IcfgLocation> worklistBackward = new ArrayDeque<>();
//				final Set<IcfgLocation> seenBackward = new HashSet<>();
//				final Set<IcfgLocation> startLocations = new HashSet<>();
//				for (final IcfgLocation predLoc : errorLoc.getIncomingNodes()) {
//					worklistBackward.add(predLoc);
//				}
//				IcfgLocation loc;
//				while (!worklistBackward.isEmpty()) {
//					loc = worklistBackward.removeFirst();
//					for (final IcfgLocation predLoc : loc.getIncomingNodes()) {
//						if (!seenBackward.contains(predLoc)) {
//							seenBackward.add(predLoc);
//							final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(predLoc);
//							if (loa != null) {
//								startLocations.add(predLoc);
//							} else {
//								if (icfg.getInitialNodes().contains(predLoc)) {
//									startLocations.add(predLoc);
//								} else {
//									worklistBackward.add(predLoc);
//								}
//							}
//						}
//					}
//				}
//				for (final IcfgLocation startLoc : startLocations) {
//					final ArrayDeque<IcfgLocation> worklistForward = new ArrayDeque<>();
//					final Set<IcfgLocation> seenForward = new HashSet<>();
//					final Set<IcfgLocation> errorLocations = new HashSet<>();
//					for (final IcfgLocation succLoc : startLoc.getOutgoingNodes()) {
//						processForward(worklistForward, seenForward, errorLocations, succLoc, false);
//					}
//					while (!worklistForward.isEmpty()) {
//						loc = worklistForward.removeFirst();
//						for (final IcfgLocation succLoc : loc.getOutgoingNodes()) {
//							if (!seenForward.contains(succLoc)) {
//								processForward(worklistForward, seenForward, errorLocations, succLoc, true);
//							}
//						}
//					}
//					seenForward.add(startLoc);
//					{
//						{
//							final BlockEncodingBacktranslator backtranslator = new BlockEncodingBacktranslator(IcfgEdge.class, Term.class, mLogger);
//							final BasicIcfg<IcfgLocation> copy = new IcfgDuplicator(mLogger, mServices, mIcfg.getCfgSmtToolkit().getManagedScript(), backtranslator).copy(mIcfg);
//							final String startLocProcedure = startLoc.getProcedure();
//							final IcfgLocation entryForStarLoc = mIcfg.getProcedureEntryNodes().get(startLocProcedure);
//							if (startLoc != entryForStarLoc) {
//								final IcfgLocation entryInCopy = entryForStarLoc;
//								final IcfgLocation startInCopy = startLoc;
//								final UnmodifiableTransFormula transFormula = TransFormulaBuilder.getTrivialTransFormula(copy.getCfgSmtToolkit().getManagedScript());
//								copy.getCfgSmtToolkit().getIcfgEdgeFactory().createInternalTransition(entryInCopy, startInCopy, new Payload(), transFormula);
//							}
//						}
//						// some code for transforming parts of a CFG into a single statement
//						final String identifier = "InductivityChecksStartingFrom_" + startLoc;
//						final PathProgramConstructionResult test = constructPathProgram(identifier, mIcfg,
//								seenForward, Collections.singleton(startLoc));
//						final IUltimateServiceProvider beServices =
//								mServices.registerPreferenceLayer(getClass(), BlockEncodingPreferences.PLUGIN_ID);
//						final IPreferenceProvider ups = beServices.getPreferenceProvider(BlockEncodingPreferences.PLUGIN_ID);
//						ups.put(BlockEncodingPreferences.FXP_REMOVE_SINK_STATES, false);
//						ups.put(BlockEncodingPreferences.FXP_REMOVE_INFEASIBLE_EDGES, false);
//						final BlockEncoder be = new BlockEncoder(mLogger, beServices, test.getPathProgram(),
//								SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
//						final IIcfg<IcfgLocation> encoded = be.getResult();
//						test.toString();
//					}
//				}
//			}
//		}
//	}
//
//	private void processForward(final ArrayDeque<IcfgLocation> worklistForward, final Set<IcfgLocation> seenForward,
//			final Set<IcfgLocation> errorLocations, final IcfgLocation succLoc, final boolean checkForErrorLocs) {
//		seenForward.add(succLoc);
//		final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(succLoc);
//		if (loa != null) {
//			final IcfgLocation eLoc = getErrorLocForLoopInvariant(succLoc);
//			seenForward.add(eLoc);
//			errorLocations.add(eLoc);
//		} else {
//			final Check check = Check.getAnnotation(succLoc);
//			if (checkForErrorLocs && check != null) {
//				seenForward.add(succLoc);
//				errorLocations.add(succLoc);
//			} else {
//				seenForward.add(succLoc);
//				worklistForward.add(succLoc);
//			}
//		}
//	}
//
//	private IcfgLocation getErrorLocForLoopInvariant(final IcfgLocation succLoc) {
//		IcfgLocation result = null;
//		for (final IcfgLocation loopSucc : succLoc.getOutgoingNodes()) {
//			final Check check = Check.getAnnotation(loopSucc);
//			if (check != null) {
//				final EnumSet<Spec> specs = check.getSpec();
////				if (specs.size() == 1) {
//					specs.contains(Spec.INVARIANT);
//					if (result == null) {
//						result = loopSucc;
//					} else {
//						throw new UnsupportedOperationException("several invariants");
//					}
////				} else {
////					throw new UnsupportedOperationException("several specs");
////				}
//			}
//		}
//		if (result == null) {
//			throw new UnsupportedOperationException("missing invariant error location");
//		}
//		return result;
//	}
//	
//	
//	
//	/**
//	 * TODO Matthias
//	 * @param identifier
//	 * @param originalIcfg
//	 * @param allowedLocations
//	 * @param additionalInitialLocations
//	 * @return
//	 */
//	public static <E extends IIcfgTransition<IcfgLocation>> PathProgramConstructionResult constructPathProgram(
//			final String identifier, final IIcfg<IcfgLocation> originalIcfg, final Set<IcfgLocation> allowedLocations,
//			final Set<IcfgLocation> additionalInitialLocations) {
//		final Set<E> allowedTransitions = new HashSet<>();
//		for (final IcfgLocation loc : allowedLocations) {
//			loc.getOutgoingEdges();
//			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
//				if (allowedLocations.contains(edge.getTarget())) {
//					allowedTransitions.add((E) edge);
//				}
//			}
//		}
//		
//		final PathProgramConstructionResult ppc = new PathProgramConstructor(originalIcfg, allowedTransitions, identifier, additionalInitialLocations)
//				.getResult();
//		final Map<IcfgLocation, IcfgLocation> old2new = ppc.getLocationMapping();
//		for (final IcfgLocation newInit : additionalInitialLocations) {
//			
//		}
//		return ppc;
//	}
}
