/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 *
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.converter;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.BlockEncodingAnnotation;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.ConfigurableHeuristic;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.DynamicHeuristic;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.StatisticBasedHeuristic;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRatingHeuristic;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;

/**
 * This class is like BlockEncoder, the start point where every function in the program is converted back to an RCFG. An
 * advantage is, that this can be executed in parallel, which gives some performance gains.
 *
 * @author Stefan Wissert
 *
 */
public class MinModelConverter {

	private final ILogger mLogger;

	private Boogie2SMT mBoogie2SMT;

	private ConversionVisitor mConvertVisitor;

	private final IUltimateServiceProvider mServices;

	/**
	 * Public Constructor.
	 */
	public MinModelConverter(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * Starting point of the back conversion to an RCFG. Note: Due to changes of data model, the minimized model belongs
	 * now as Annotation at the RootEdges.
	 *
	 * @param rootNode
	 *            the rootNode to convert
	 * @return the converted rootNode
	 */
	public RootNode startConversion(final RootNode root) {
		final RootNode newRoot = new RootNode(ILocation.getAnnotation(root), root.getRootAnnot());
		ModelUtils.copyAnnotations(root, newRoot);
		mBoogie2SMT = root.getRootAnnot().getBoogie2SMT();
		final boolean simplify = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_SIMPLIFY);
		mConvertVisitor = new ConversionVisitor(mBoogie2SMT, root, getRatingHeuristic(), mServices, simplify);
		for (final IcfgEdge edge : root.getOutgoingEdges()) {
			if (edge instanceof RootEdge) {
				final BlockEncodingAnnotation annot = BlockEncodingAnnotation.getAnnotation(edge);
				if (annot != null) {
					ModelUtils.copyAnnotations(edge, new RootEdge(newRoot, convertFunction(annot.getNode())));
				} else {
					mLogger.warn("Conversion cancelled, illegal RCFG!");
					throw new IllegalArgumentException("The target of an root edge is not a MinimizedNode");
				}
			} else {
				mLogger.warn("Conversion cancelled, illegal RCFG!");
				throw new IllegalArgumentException("An outgoing edge of RootNode is not a RootEdge");
			}
		}
		// Now we have to update the RootAnnot, which is created while executing
		// the RCFGBuilder (this is needed for example for the
		// HoareAnnotations)
		updateRootAnnot(newRoot.getRootAnnot());
		mLogger.info(EncodingStatistics.reportStatistics());
		return newRoot;
	}

	/**
	 * Checks the preferences for a given rating bound.
	 *
	 * @return gets the rating boundary
	 */
	private IRatingHeuristic getRatingHeuristic() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String prefValue = prefs.getString(PreferenceInitializer.LABEL_RATINGBOUND);
		final RatingStrategy strategy = prefs.getEnum(PreferenceInitializer.LABEL_STRATEGY, RatingStrategy.class);
		// if there is no boundary value given, we do Large Block Encoding
		if (strategy == RatingStrategy.LARGE_BLOCK || prefValue.isEmpty()) {
			return null;
		}
		// check if we should use the statistic based heuristic
		if (prefs.getBoolean(PreferenceInitializer.LABEL_USESTATHEURISTIC)) {
			final StatisticBasedHeuristic heuristic = new StatisticBasedHeuristic(strategy, mLogger);
			// maybe the case that there is no supported heuristic, then we use
			// Large Block Encoding
			if (!heuristic.isRatingStrategySupported(strategy)) {
				return null;
			}
			heuristic.init(prefValue);
			return heuristic;
		} else if (prefs.getBoolean(PreferenceInitializer.LABEL_USEDYNAMICHEURISTIC)) {
			final DynamicHeuristic heuristic = new DynamicHeuristic(strategy);
			// maybe the case that there is no supported heuristic, then we use
			// Large Block Encoding
			if (!heuristic.isRatingStrategySupported(strategy)) {
				return null;
			}
			heuristic.init(prefValue);
			return heuristic;
		} else {
			final ConfigurableHeuristic heuristic = new ConfigurableHeuristic(strategy);
			heuristic.init(prefValue);
			return heuristic;
		}
	}

	/**
	 * Converts a function (given as MinimizedNode) by calling the ConversionVisitor.
	 *
	 * @param node
	 *            function head
	 * @return converted ProgramPoint
	 */
	private BoogieIcfgLocation convertFunction(final MinimizedNode node) {
		final BoogieIcfgLocation newNode = mConvertVisitor.getReferencedNode(node);
		// To do the conversion, we need to run over the minimized graph,
		// and convert every edge into an regular RCFG edge
		// ---> to do this we need some special Visitor which does the
		// conversion
		mConvertVisitor.init(newNode);
		mConvertVisitor.visitNode(node);
		return newNode;
	}

	/**
	 * We have to update some Maps, which are stored in the RootAnnot. They are needed for several computations
	 * afterwards. Most of the maps are usual very small, so that iterating over them should be not that expensive. One
	 * exception is the field "locNodes", there is every ProgramPoint stored, with its name and the procedure name. We
	 * store during the conversion.
	 *
	 * @param rootAnnot
	 */
	private void updateRootAnnot(final BoogieIcfgContainer rootAnnot) {
		final HashMap<BoogieIcfgLocation, BoogieIcfgLocation> progPointMap = mConvertVisitor.getOrigToNewMap();
		// Update the Entry-Nodes
		final HashMap<String, BoogieIcfgLocation> entryNodes = new HashMap<>(rootAnnot.getProcedureEntryNodes());
		rootAnnot.getProcedureEntryNodes().clear();
		for (final String key : entryNodes.keySet()) {
			final BoogieIcfgLocation oldVal = entryNodes.get(key);
			if (progPointMap.containsKey(oldVal)) {
				rootAnnot.getProcedureEntryNodes().put(key, progPointMap.get(oldVal));
			}
		}
		// Update the Exit-Nodes
		final HashMap<String, BoogieIcfgLocation> exitNodes = new HashMap<>(rootAnnot.getProcedureExitNodes());
		rootAnnot.getProcedureExitNodes().clear();
		for (final String key : exitNodes.keySet()) {
			final BoogieIcfgLocation oldVal = exitNodes.get(key);
			if (progPointMap.containsKey(oldVal)) {
				rootAnnot.getProcedureExitNodes().put(key, progPointMap.get(oldVal));
			}
		}
		// Update the Error-Nodes
		for (final String key : rootAnnot.getProcedureErrorNodes().keySet()) {
			final Set<BoogieIcfgLocation> newReferences = new HashSet<>();
			for (final BoogieIcfgLocation oldVal : rootAnnot.getProcedureErrorNodes().get(key)) {
				if (progPointMap.containsKey(oldVal)) {
					newReferences.add(progPointMap.get(oldVal));
				} else {
					mLogger.warn(
							"There is no correspondent node in the" + " new graph for the error location " + oldVal);
				}
			}
			rootAnnot.getProcedureErrorNodes().put(key, newReferences);
		}
		// Update the LoopLocations
		// Attention: ProgramPoint implements equals, we have to care for that!
		final Set<BoogieIcfgLocation> keySet = new HashSet<>(rootAnnot.getLoopLocations());
		rootAnnot.getLoopLocations().clear();
		for (final BoogieIcfgLocation oldVal : keySet) {
			if (progPointMap.containsKey(oldVal)) {
				final BoogieIcfgLocation newVal = progPointMap.get(oldVal);
				if (newVal.getBoogieASTNode() != null) {
					// Since hashCode(oldVal) == hashCode(newVal), this line
					// overwrites the old entry, so that we do not remove it in
					// the end!
					rootAnnot.getLoopLocations().add(newVal);
				}
			}
		}
		// update the locNodes, we rely here on the visitor
		rootAnnot.getProgramPoints().clear();
		rootAnnot.getProgramPoints().putAll(mConvertVisitor.getLocNodesForAnnot());
	}
}
