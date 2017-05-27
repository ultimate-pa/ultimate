
/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Jonas Werner (jonaswerner95@gmail.com)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.ExampleLoopAccelerationTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * A basic IcfgTransformer that applies the
 * {@link ExampleLoopAccelerationTransformulaTransformer}, i.e., replaces all
 * transformulas of an {@link IIcfg} with a new instance. + First tries for loop
 * acceleration.
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */

public class WernerLoopAccelerationIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {
	private final ILogger mLogger;
	private final Deque<Loop> mLoopBodies;
	private final LoopDetector<INLOC> mLoopDetector;
	private final IIcfg<OUTLOC> mResult;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final IIcfgSymbolTable mOldSymbolTable;

	/**
	 * Construct a new Loop Acceleration Icfg Transformer.
	 * 
	 * @param logger
	 * @param originalIcfg
	 * @param funLocFac
	 * @param backtranslationTracker
	 * @param outLocationClass
	 * @param newIcfgIdentifier
	 * @param transformer
	 * @param services
	 */
	public WernerLoopAccelerationIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IUltimateServiceProvider services) {

		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mScript = origIcfg.getCfgSmtToolkit().getManagedScript();
		mLogger = Objects.requireNonNull(logger);
		mServices = services;
		mLoopDetector = new LoopDetector<>(mLogger, origIcfg, mServices, mScript);
		mOldSymbolTable = originalIcfg.getCfgSmtToolkit().getSymbolTable();

		mLoopBodies = mLoopDetector.getLoopBodies();

		mResult = transform(originalIcfg, funLocFac, backtranslationTracker, outLocationClass, newIcfgIdentifier,
				transformer);
	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer) {

		transformer.preprocessIcfg(originalIcfg);

		for (final Loop loop : mLoopBodies) {
			final List<TermVariable> pathCounter = new ArrayList<>();
			for (final Backbone backbone : loop.getBackbones()) {

				final UnmodifiableTransFormula tf = (UnmodifiableTransFormula) backbone.getFormula();
								
				mLogger.debug("Backbone Formula: " + tf);
				
				final SimultaneousUpdate update = new SimultaneousUpdate(tf, mScript);
				
				mLogger.debug("updated vars: " + update.getUpdatedVars());
				
				final SymbolicMemory symbolicMemory = new SymbolicMemory(mScript, mLogger, tf, mOldSymbolTable);
				symbolicMemory.updateVars(update.getUpdatedVars());
				final Term condition = symbolicMemory.updateCondition(TransFormulaUtils.computeGuard(tf, mScript, mServices,
						mLogger));		
								
				final TermVariable backbonePathCounter = mScript.constructFreshTermVariable("kappa",
						mScript.getScript().sort(SmtSortUtils.INT_SORT));

				pathCounter.add(backbonePathCounter);
				mLogger.debug(backbonePathCounter);
				backbone.setPathCounter(backbonePathCounter);
				backbone.setCondition(condition);
				
				mLogger.debug("Backbone Condition: " + backbone.getCondition());
				
				backbone.setSymbolicMemory(symbolicMemory);
			}

			final IteratedSymbolicMemory iteratedSymbolicMemory = new IteratedSymbolicMemory(mScript, mLogger,
					loop.getFormula(), mOldSymbolTable, loop, pathCounter);

			iteratedSymbolicMemory.updateMemory();
			iteratedSymbolicMemory.updateCondition();
		}

		final BasicIcfg<OUTLOC> resultIcfg = new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(),
				outLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(funLocFac,
				backtranslationTracker, transformer, originalIcfg, resultIcfg);
		processLocations(originalIcfg.getInitialNodes(), lst);
		lst.finish();

		return resultIcfg;
	}

	private void processLocations(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}

			final OUTLOC newSource = lst.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				final INLOC oldTarget = (INLOC) oldTransition.getTarget();
				open.add(oldTarget);
				final OUTLOC newTarget = lst.createNewLocation(oldTarget);
				lst.createNewTransition(newSource, newTarget, oldTransition);
			}
		}
	}

	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}
