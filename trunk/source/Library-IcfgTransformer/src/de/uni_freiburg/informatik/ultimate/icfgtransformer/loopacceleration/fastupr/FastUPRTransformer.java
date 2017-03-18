/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.lang.annotation.Target;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;

/**
 * The main class for Fast Acceleration of Ultimately Periodic Relations
 * 
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 * 
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class FastUPRTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final IIcfg<OUTLOC> mResultIcfg;
	private final ManagedScript mManagedScript;
	private final Map<INLOC, OUTLOC> mOldLoc2NewLoc;
	private final Map<IIcfgCallTransition<INLOC>, IcfgCallTransition> mOldCalls2NewCalls;
	private IBacktranslationTracker mBacktranslationTracker;
	private ILocationFactory<INLOC, OUTLOC> mLocationFactory;

	public FastUPRTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Class<OUTLOC> outLocationClass, 
			final ILocationFactory<INLOC, OUTLOC> locationFactory, String newIcfgIdentifier, ITransformulaTransformer transformer,
			final IBacktranslationTracker backtranslationTracker, IUltimateServiceProvider services) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mLocationFactory = (ILocationFactory<INLOC, OUTLOC>) Objects.requireNonNull(locationFactory);
		mManagedScript = origIcfg.getCfgSmtToolkit().getManagedScript();
		mOldLoc2NewLoc = new HashMap<>();
		mOldCalls2NewCalls = new HashMap<>();
		mBacktranslationTracker = (IBacktranslationTracker) backtranslationTracker;

		
		
		// perform transformation last
		mLogger.debug("Starting fastUPR Transformation");
		mResultIcfg = transform(origIcfg, Objects.requireNonNull(newIcfgIdentifier),
				Objects.requireNonNull(outLocationClass), transformer);
	}


	@SuppressWarnings("unchecked")
	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final String newIcfgIdentifier,
			final Class<OUTLOC> outLocationClass, ITransformulaTransformer transformer) {
		
		
		mLogger.debug("Getting List of loop paths ...");
		
		final FastUPRDetection loopDetection = new FastUPRDetection<>(mLogger, originalIcfg, outLocationClass, newIcfgIdentifier);
		final List<Deque<INLOC>> loopPaths = loopDetection.getLoopPaths();
		
		if (loopPaths.size() < 1) { 
			mLogger.debug("No loop paths found");
		} else {
			mLogger.debug("Found " + loopPaths.size() + " loop paths");
		}
		
		final BasicIcfg<OUTLOC> resultIcfg = new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		

		final TransformedIcfgBuilder<INLOC, OUTLOC> lst =
				new TransformedIcfgBuilder<>(mLocationFactory, mBacktranslationTracker, transformer, originalIcfg, resultIcfg);
		
		mLogger.debug("Transforming loop into icfg...");
		
		getLoopIcfg(loopPaths, resultIcfg, originalIcfg, lst);
		
		mLogger.debug("Icfg created.");
		
		final IIcfgSymbolTable origSymbolTable = originalIcfg.getSymboltable();
		final ReplacementVarFactory fac = new ReplacementVarFactory(resultIcfg.getCfgSmtToolkit(), false);

		final Set<INLOC> init = originalIcfg.getInitialNodes();
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();
		
		return resultIcfg;
	}

	@SuppressWarnings("unchecked")
	private void getLoopIcfg(List<Deque<INLOC>> loopPaths, final BasicIcfg<OUTLOC> result, final IIcfg<INLOC> origIcfg,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {
		// TODO: actual loop path, maybe split in three? 
		// 1 - before loop
		// 2 - during loop
		// 3 - after loop
		
		
		
		final Deque<INLOC> path = loopPaths.get(0);
		
		final Set<INLOC> init = origIcfg.getInitialNodes();
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();
		final Deque<INLOC> afterLoop = new ArrayDeque<>();
		
		mLogger.debug("Starting main transformation loop...");
		
		while(!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			
			if (!closed.add(oldSource)) continue;
			
			final OUTLOC newSource = lst.createNewLocation(oldSource);
			
			createNewLocations(oldSource, newSource, closed, result, lst);			
		}
	}
	
	private void createNewLocations(final INLOC oldSource, final OUTLOC newSource, final Set<INLOC> closed,
			final BasicIcfg<OUTLOC> result, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		result.addOrdinaryLocation(newSource);

		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {
			final INLOC oldTarget = (INLOC) oldEdge.getTarget();
			final OUTLOC newTarget = lst.createNewLocation(oldTarget);
			final IcfgEdge newEdge = lst.createNewTransition(newSource, newTarget, oldEdge);
			newSource.addOutgoing(newEdge);
			newTarget.addIncoming(newEdge);
			
			if(!closed.add(oldTarget)) return;
			
			createNewLocations(oldTarget, newTarget, closed, result, lst);
		}
		
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}

}
