/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.IcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BlockEncodingObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final BlockEncodingBacktranslator mBacktranslator;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;

	private IIcfg<?> mResult;

	public BlockEncodingObserver(final ILogger logger, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final SimplificationTechnique simplTech,
			final XnfConversionTechnique xnfConvTech) {
		mLogger = logger;
		mServices = services;
		mBacktranslator = backtranslator;
		mSimplificationTechnique = simplTech;
		mXnfConversionTechnique = xnfConvTech;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// no initialization needed
	}

	@Override
	public void finish() throws Throwable {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getModel() {
		return mResult;
	}

	@Override
	public boolean process(final IElement root) throws Exception {
		if (root instanceof IIcfg<?>) {
			final IIcfg<?> originalIcfg = (IIcfg<?>) root;
			final IcfgEdgeBuilder edgeBuilder = new IcfgEdgeBuilder(originalIcfg.getCfgSmtToolkit(), mServices,
					mSimplificationTechnique, mXnfConversionTechnique);
			final BasicIcfg<IcfgLocation> copiedIcfg = createIcfgCopy(edgeBuilder, originalIcfg);

			mResult = new BlockEncoder(mLogger, mServices, mBacktranslator, edgeBuilder, copiedIcfg).getResult();
			return false;
		}
		return true;
	}

	private BasicIcfg<IcfgLocation> createIcfgCopy(final IcfgEdgeBuilder edgeBuilder,
			final IIcfg<? extends IcfgLocation> icfg) {
		final BasicIcfg<IcfgLocation> newIcfg =
				new BasicIcfg<>(icfg.getIdentifier() + "_BEv2", icfg.getCfgSmtToolkit(), IcfgLocation.class);
		ModelUtils.copyAnnotations(icfg, newIcfg);

		final Map<IcfgLocation, IcfgLocation> old2new = new HashMap<>();
		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);
		final Set<Pair<IcfgLocation, IcfgEdge>> openReturns = new HashSet<>();
		// first, copy all locations
		while (iter.hasNext()) {
			final IcfgLocation oldLoc = iter.next();
			final String proc = oldLoc.getProcedure();
			final IcfgLocation newLoc = new IcfgLocation(oldLoc.getDebugIdentifier(), proc);
			ModelUtils.copyAnnotations(oldLoc, newLoc);

			final boolean isError = icfg.getProcedureErrorNodes().get(proc) != null
					&& icfg.getProcedureErrorNodes().get(proc).contains(oldLoc);
			newIcfg.addLocation(newLoc, icfg.getInitialNodes().contains(oldLoc), isError,
					oldLoc.equals(icfg.getProcedureEntryNodes().get(proc)),
					oldLoc.equals(icfg.getProcedureExitNodes().get(proc)), icfg.getLoopLocations().contains(oldLoc));
			old2new.put(oldLoc, newLoc);
		}

		assert noEdges(newIcfg) : "Icfg contains edges but should not";

		// second, add all non-return edges
		for (final Entry<IcfgLocation, IcfgLocation> nodePair : old2new.entrySet()) {
			final IcfgLocation newSource = nodePair.getValue();
			for (final IcfgEdge oldEdge : nodePair.getKey().getOutgoingEdges()) {
				if (oldEdge instanceof IIcfgReturnTransition<?, ?>) {
					// delay creating returns until everything else is processed
					openReturns.add(new Pair<>(newSource, oldEdge));
				} else {
					if (oldEdge instanceof Summary) {
						// hack to prevent copying "useless" summary edges
						final Summary oldSummary = (Summary) oldEdge;
						if (oldSummary.calledProcedureHasImplementation()) {
							continue;
						}
					}
					createEdgeCopy(edgeBuilder, old2new, newSource, oldEdge);
				}
			}
		}

		// third, add all previously ignored return edges
		openReturns.stream().forEach(a -> createEdgeCopy(edgeBuilder, old2new, a.getFirst(), a.getSecond()));

		if (mLogger.isDebugEnabled()) {
			new IcfgLocationIterator<>(newIcfg).asStream().forEach(a -> {
				mLogger.debug("Annotations of " + a);
				ModelUtils.consumeAnnotations(a, x -> mLogger.debug(x.getClass()));
			});
		}
		return newIcfg;
	}

	private boolean noEdges(final IIcfg<IcfgLocation> icfg) {

		final Set<IcfgLocation> programPoints = icfg.getProgramPoints().entrySet().stream()
				.flatMap(a -> a.getValue().entrySet().stream()).map(a -> a.getValue()).collect(Collectors.toSet());
		for (final IcfgLocation loc : programPoints) {
			if (loc.getOutgoingEdges().isEmpty() && loc.getIncomingEdges().isEmpty()) {
				continue;
			}
			mLogger.fatal("Location " + loc + " contains incoming or outgoing edges");
			mLogger.fatal("Incoming: " + loc.getIncomingEdges());
			mLogger.fatal("Outgoing: " + loc.getOutgoingEdges());
			return false;
		}

		return true;
	}

	private void createEdgeCopy(final IcfgEdgeBuilder edgeBuilder, final Map<IcfgLocation, IcfgLocation> old2new,
			final IcfgLocation newSource, final IcfgEdge oldEdge) {
		final IcfgLocation newTarget = old2new.get(oldEdge.getTarget());
		assert newTarget != null;
		final IcfgEdge newEdge = edgeBuilder.constructCopy(newSource, newTarget, oldEdge);
		mBacktranslator.mapEdges(newEdge, oldEdge);
	}

}
