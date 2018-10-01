/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ActionUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IForkActionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IJoinActionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The {@link IcfgDuplicator} copies any {@link IIcfg} and provides a new {@link BasicIcfg}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class IcfgDuplicator {

	private final ILogger mLogger;
	private final BlockEncodingBacktranslator mBacktranslator;
	private final Map<IIcfgCallTransition<IcfgLocation>, IIcfgCallTransition<IcfgLocation>> mCallCache;
	private final ManagedScript mManagedScript;
	private final Map<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>> mOld2New;

	public IcfgDuplicator(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BlockEncodingBacktranslator backtranslator) {
		mLogger = logger;
		mBacktranslator = backtranslator;
		mCallCache = new HashMap<>();
		mManagedScript = Objects.requireNonNull(managedScript);
		mOld2New = new HashMap<>();
	}

	public BasicIcfg<IcfgLocation> copy(final IIcfg<?> originalIcfg) {
		final BasicIcfg<IcfgLocation> newIcfg =
				new BasicIcfg<>(((IIcfg<? extends IcfgLocation>) originalIcfg).getIdentifier() + "_BEv2",
						originalIcfg.getCfgSmtToolkit(), IcfgLocation.class);
		ModelUtils.copyAnnotations(originalIcfg, newIcfg);

		final Map<IcfgLocation, IcfgLocation> old2new = new HashMap<>();

		// iterator over all locations, begin at all procedure entries
		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(originalIcfg.getProcedureEntryNodes().values());
		final Set<Pair<IcfgLocation, IcfgEdge>> openReturns = new HashSet<>();

		// first, copy all locations
		while (iter.hasNext()) {
			final IcfgLocation oldLoc = iter.next();
			final String proc = oldLoc.getProcedure();
			final IcfgLocation newLoc = createLocCopy(oldLoc);

			final boolean isError = originalIcfg.getProcedureErrorNodes().get(proc) != null
					&& originalIcfg.getProcedureErrorNodes().get(proc).contains(oldLoc);
			newIcfg.addLocation(newLoc, originalIcfg.getInitialNodes().contains(oldLoc), isError,
					oldLoc.equals(originalIcfg.getProcedureEntryNodes().get(proc)),
					oldLoc.equals(originalIcfg.getProcedureExitNodes().get(proc)),
					originalIcfg.getLoopLocations().contains(oldLoc));
			old2new.put(oldLoc, newLoc);
		}

		assert noEdges(newIcfg) : "Icfg contains edges but should not";

		final IcfgEdgeFactory edgeFactory = newIcfg.getCfgSmtToolkit().getIcfgEdgeFactory();
		// second, add all non-return edges
		for (final Entry<IcfgLocation, IcfgLocation> nodePair : old2new.entrySet()) {
			final IcfgLocation newSource = nodePair.getValue();
			for (final IcfgEdge oldEdge : nodePair.getKey().getOutgoingEdges()) {
				if (oldEdge instanceof IIcfgReturnTransition<?, ?>) {
					// delay creating returns until everything else is processed
					openReturns.add(new Pair<>(newSource, oldEdge));
					continue;
				}
				if (oldEdge instanceof IIcfgSummaryTransition) {
					// hack to prevent copying "useless" summary edges
					final IIcfgSummaryTransition oldSummary = (IIcfgSummaryTransition) oldEdge;
					if (oldSummary.calledProcedureHasImplementation()) {
						continue;
					}
				}
				createEdgeCopy(old2new, newSource, oldEdge, edgeFactory);
			}
		}

		// third, add all previously ignored return edges
		openReturns.stream().forEach(a -> createEdgeCopy(old2new, a.getFirst(), a.getSecond(), edgeFactory));
		mBacktranslator.removeIntermediateMappings();
		return newIcfg;
	}

	private IcfgLocation createLocCopy(final IcfgLocation oldLoc) {
		final IcfgLocation newLoc = new IcfgLocation(oldLoc.getDebugIdentifier(), oldLoc.getProcedure());
		ModelUtils.copyAnnotations(oldLoc, newLoc);
		mBacktranslator.mapLocations(newLoc, oldLoc);
		return newLoc;
	}

	private boolean noEdges(final IIcfg<IcfgLocation> icfg) {

		final Set<IcfgLocation> programPoints =
				icfg.getProgramPoints().entrySet().stream().flatMap(a -> a.getValue().entrySet().stream())
						.map(Entry<DebugIdentifier, IcfgLocation>::getValue).collect(Collectors.toSet());
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

	private IcfgEdge createEdgeCopy(final Map<IcfgLocation, IcfgLocation> old2new, final IcfgLocation newSource,
			final IcfgEdge oldEdge, final IcfgEdgeFactory edgeFactory) {
		final IcfgLocation newTarget = old2new.get(oldEdge.getTarget());
		assert newTarget != null;
		final IcfgEdge newEdge = createUnconnectedCopy(newSource, newTarget, oldEdge, edgeFactory);
		newSource.addOutgoing(newEdge);
		newTarget.addIncoming(newEdge);
		ModelUtils.copyAnnotations(oldEdge, newEdge);
		mBacktranslator.mapEdges(newEdge, oldEdge);
		mOld2New.put(oldEdge, newEdge);
		return newEdge;
	}

	@SuppressWarnings("unchecked")
	private IcfgEdge createUnconnectedCopy(final IcfgLocation newSource, final IcfgLocation newTarget,
			final IIcfgTransition<?> oldEdge, final IcfgEdgeFactory edgeFactory) {
		// contains transformula copy
		final IAction newAction = ActionUtils.constructCopy(mManagedScript, oldEdge);

		final IcfgEdge rtr;
		if (oldEdge instanceof IIcfgInternalTransition<?>) {
			rtr = edgeFactory.createInternalTransition(newSource, newTarget, null, newAction.getTransformula());
		} else if (oldEdge instanceof IIcfgCallTransition<?>) {
			rtr = createCopyCall(newSource, newTarget, oldEdge, newAction, edgeFactory);
		} else if (oldEdge instanceof IIcfgReturnTransition<?, ?>) {
			final IIcfgReturnTransition<?, ?> oldReturn = (IIcfgReturnTransition<?, ?>) oldEdge;
			final IIcfgCallTransition<?> oldCorrespondingCall = oldReturn.getCorrespondingCall();
			IIcfgCallTransition<IcfgLocation> correspondingCall = mCallCache.get(oldCorrespondingCall);
			if (correspondingCall == null) {
				mLogger.warn("Creating raw copy for unreachable call because return is reachable in graph view: "
						+ oldCorrespondingCall);
				correspondingCall = (IIcfgCallTransition<IcfgLocation>) createUnconnectedCopy(null, null,
						oldCorrespondingCall, edgeFactory);
			}
			final IReturnAction rAction = (IReturnAction) newAction;
			rtr = edgeFactory.createReturnTransition(newSource, newTarget, correspondingCall, null,
					rAction.getAssignmentOfReturn(), rAction.getLocalVarsAssignmentOfCall());
		} else if (oldEdge instanceof IIcfgForkTransitionThreadCurrent) {
			final IForkActionThreadCurrent fAction = (IForkActionThreadCurrent) newAction;
			rtr = edgeFactory.createForkThreadCurrentTransition(newSource, newTarget, null, fAction.getTransformula(),
					fAction.getForkSmtArguments(), fAction.getNameOfForkedProcedure());
		} else if (oldEdge instanceof IIcfgJoinTransitionThreadCurrent) {
			final IJoinActionThreadCurrent jAction = (IJoinActionThreadCurrent) newAction;
			rtr = edgeFactory.createJoinThreadCurrentTransition(newSource, newTarget, null, jAction.getTransformula(),
					jAction.getJoinSmtArguments());
		} else {
			throw new UnsupportedOperationException("Unknown IcfgEdge subtype: " + oldEdge.getClass());
		}
		return rtr;
	}

	private IcfgEdge createCopyCall(final IcfgLocation source, final IcfgLocation target,
			final IIcfgTransition<?> oldEdge, final IAction newAction, final IcfgEdgeFactory edgeFactory) {
		final IcfgEdge rtr;
		final ICallAction cAction = (ICallAction) newAction;
		rtr = edgeFactory.createCallTransition(source, target, null, cAction.getLocalVarsAssignment());
		mCallCache.put((IIcfgCallTransition<IcfgLocation>) oldEdge, (IIcfgCallTransition<IcfgLocation>) rtr);
		return rtr;
	}

	public Map<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>> getOld2NewEdgeMapping() {
		return Collections.unmodifiableMap(mOld2New);
	}

}
