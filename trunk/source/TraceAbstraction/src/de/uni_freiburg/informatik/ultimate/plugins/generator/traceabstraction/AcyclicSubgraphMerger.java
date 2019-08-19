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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IcfgDuplicator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncoder;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.BlockEncodingPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram.PathProgramConstructionResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Merge an acyclic subgraph into a list of {@link UnmodifiableTransFormula}s. Given
 * <ul>
 * <li>an ICFG mICFG,
 * <li>a set of {@link IcfgEdge}s that defines an acyclic and connected subgraph of mICFG,
 * <li>a location startLoc such that all edges of the subgraph are successors of startLoc,
 * <li>and a a set of locations {endLoc_1, ..., endloc L_n},
 * </ul>
 * construct {@link UnmodifiableTransFormula}s tf_1,...tf_n such that tf_i represents the disjunction of all paths from
 * startLoc to endLoc_i.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class AcyclicSubgraphMerger {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final Map<IcfgLocation, UnmodifiableTransFormula> mEndloc2TransFormula;

	public AcyclicSubgraphMerger(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final Set<IcfgEdge> subgraphEdges, final IcfgLocation subgraphStartLocation,
			final IcfgEdge startLocErrorEdge, final Set<IcfgLocation> subgraphEndLocations) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final Subgraph initialSubgraph = new Subgraph(icfg, subgraphStartLocation, subgraphEndLocations);

		final Subgraph initialCopy;
		Set<IcfgEdge> subgraphEdgesInCopy;
		{
			// construct a copy of the cfg
			final Subgraph initialCopyWithOldStartLoc;
			final IcfgEdge startLocErrorEdgeInCopy;
			{
				final BlockEncodingBacktranslator backtranslator =
						new BlockEncodingBacktranslator(IcfgEdge.class, Term.class, mLogger);
				final BasicIcfg<IcfgLocation> newCfg = new IcfgDuplicator(mLogger, mServices,
						icfg.getCfgSmtToolkit().getManagedScript(), backtranslator).copy(icfg);
				final Map<IcfgLocation, IcfgLocation> newLoc2oldLoc = backtranslator.getLocationMapping();
				initialCopyWithOldStartLoc = new Subgraph(initialSubgraph, newCfg, newLoc2oldLoc);
				final Map<IcfgEdge, IcfgEdge> newEdge2oldEdge = (Map) backtranslator.getEdgeMapping();
				final Map<IcfgEdge, IcfgEdge> oldEdge2newEdge =
						DataStructureUtils.constructReverseMapping(newEdge2oldEdge);
				subgraphEdgesInCopy = translate(subgraphEdges, oldEdge2newEdge);
				if (startLocErrorEdge == null) {
					startLocErrorEdgeInCopy = null;
				} else {
					startLocErrorEdgeInCopy = oldEdge2newEdge.get(startLocErrorEdge);
					Objects.requireNonNull(startLocErrorEdgeInCopy);
				}
			}

			final String startLocProcedure = initialCopyWithOldStartLoc.getSubgraphStartLocation().getProcedure();
			final IcfgLocation entryForStartLoc =
					initialCopyWithOldStartLoc.getIcfg().getProcedureEntryNodes().get(startLocProcedure);
			// take the entry of the startLocations's procedure and connect entry
			// and starLocation by TransFormula that is labeled with 'true' (a skip
			// edge)
			// one exception: if entry is already start location then we do not add
			// edges
			if (initialSubgraph.getSubgraphStartLocation() != entryForStartLoc) {
				final List<IcfgEdge> initOutgoing =
						new ArrayList<>(initialCopyWithOldStartLoc.getSubgraphStartLocation().getOutgoingEdges());
				for (final IcfgEdge edge : initOutgoing) {
					if (edge != startLocErrorEdgeInCopy && subgraphEdgesInCopy.contains(edge)) {
						// hashcode changes, we should remove and re-add it
						subgraphEdgesInCopy.remove(edge);
						edge.redirectSource(entryForStartLoc);
						subgraphEdgesInCopy.add(edge);
					}
				}
				initialCopy = new Subgraph(initialCopyWithOldStartLoc, entryForStartLoc);
			} else {
				initialCopy = initialCopyWithOldStartLoc;
			}
		}

		final Subgraph projection;
		{
			final String identifier = "InductivityChecksStartingFrom_" + initialCopy.getSubgraphStartLocation();
			final PathProgramConstructionResult pc =
					PathProgram.constructPathProgram(identifier, initialCopy.getIcfg(), subgraphEdgesInCopy);
			final Map<IcfgLocation, IcfgLocation> copy2projection = pc.getLocationMapping();
			final Map<IcfgLocation, IcfgLocation> projection2copy =
					DataStructureUtils.constructReverseMapping(copy2projection);
			projection = new Subgraph(initialCopy, pc.getPathProgram(), projection2copy);
		}

		// apply block encoding
		final Subgraph blockEncoded;
		{
			final IUltimateServiceProvider beServices =
					mServices.registerDefaultPreferenceLayer(getClass(), BlockEncodingPreferences.PLUGIN_ID);
			final IPreferenceProvider ups = beServices.getPreferenceProvider(BlockEncodingPreferences.PLUGIN_ID);
			ups.put(BlockEncodingPreferences.FXP_REMOVE_SINK_STATES, false);
			ups.put(BlockEncodingPreferences.FXP_REMOVE_INFEASIBLE_EDGES, false);
			final BlockEncoder be = new BlockEncoder(mLogger, beServices, projection.getIcfg(),
					SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
			blockEncoded = new Subgraph(projection, be.getResult(), be.getBacktranslator().getLocationMapping());
		}

		if (blockEncoded.getSubgraphStartLocation().getOutgoingEdges().size() != initialSubgraph
				.getSubgraphEndLocations().size()) {
			throw new AssertionError("Either subgraph not acyclic or there is a bug");
		}

		mEndloc2TransFormula = new HashMap<>();
		for (final IcfgEdge startSucc : blockEncoded.getSubgraphStartLocation().getOutgoingEdges()) {
			if (!blockEncoded.getSubgraphEndLocations().contains(startSucc.getTarget())) {
				throw new AssertionError();
			}
			final IcfgLocation endLoc = startSucc.getTarget();
			final IcfgLocation endInProjection = blockEncoded.getBacktranslation().get(endLoc);
			final IcfgLocation endInInitialCopy = projection.getBacktranslation().get(endInProjection);
			final IcfgLocation endInInput = initialCopy.getBacktranslation().get(endInInitialCopy);
			mEndloc2TransFormula.put(endInInput, startSucc.getTransformula());
		}
	}

	/**
	 * @return {@link UnmodifiableTransFormula} that represents the disjunction of all paths from startLoc to endLoc.
	 */
	public UnmodifiableTransFormula getTransFormula(final IcfgLocation endLoc) {
		return mEndloc2TransFormula.get(endLoc);
	}

	private class Subgraph {
		private final IIcfg<IcfgLocation> mIcfg;
		private final IcfgLocation mSubgraphStartLocation;
		private final Set<IcfgLocation> mSubgraphEndLocations;
		private final Map<IcfgLocation, IcfgLocation> mBacktranslation;
		private final Map<IcfgLocation, IcfgLocation> mForwardTranslation;

		public Subgraph(final IIcfg<IcfgLocation> icfg, final IcfgLocation subgraphStartLocation,
				final Set<IcfgLocation> subgraphEndLocations) {
			super();
			mIcfg = icfg;
			mSubgraphStartLocation = subgraphStartLocation;
			mSubgraphEndLocations = subgraphEndLocations;
			mBacktranslation = null;
			mForwardTranslation = null;
		}

		public Subgraph(final Subgraph oldSubgraph, final IIcfg<IcfgLocation> newIcfg,
				final Map<IcfgLocation, IcfgLocation> backtranslation) {
			mIcfg = newIcfg;
			mBacktranslation = backtranslation;
			mForwardTranslation = DataStructureUtils.constructReverseMapping(backtranslation);
			mSubgraphStartLocation = mForwardTranslation.get(oldSubgraph.getSubgraphStartLocation());
			Objects.requireNonNull(mSubgraphStartLocation);
			mSubgraphEndLocations = translate(oldSubgraph.getSubgraphEndLocations(), mForwardTranslation);
		}

		/**
		 * Constructor for changing startLocation
		 */
		public Subgraph(final Subgraph subgraph, final IcfgLocation newStartLocation) {
			mIcfg = subgraph.getIcfg();
			mBacktranslation = subgraph.getBacktranslation();
			mForwardTranslation = subgraph.getForwardTranslation();
			mSubgraphStartLocation = newStartLocation;
			Objects.requireNonNull(mSubgraphStartLocation);
			mSubgraphEndLocations = subgraph.getSubgraphEndLocations();
		}

		public IIcfg<IcfgLocation> getIcfg() {
			return mIcfg;
		}

		public IcfgLocation getSubgraphStartLocation() {
			return mSubgraphStartLocation;
		}

		public Set<IcfgLocation> getSubgraphEndLocations() {
			return mSubgraphEndLocations;
		}

		public Map<IcfgLocation, IcfgLocation> getBacktranslation() {
			return mBacktranslation;
		}

		public Map<IcfgLocation, IcfgLocation> getForwardTranslation() {
			return mForwardTranslation;
		}

		@Override
		public String toString() {
			return CFG2NestedWordAutomaton.printIcfg(mServices, mIcfg);
		}

	}

	private <K, V> Set<V> translate(final Set<K> set, final Map<K, V> map) {
		// Set<V> result = new HashSet<>();
		// for (K elem : set) {
		// result.add(map.get(elem));
		// }
		// return result;
		return set.stream().map(map::get).collect(Collectors.toSet());
	}

}
