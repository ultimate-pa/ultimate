
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
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.ExampleLoopAccelerationTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;
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
	private final Map<IcfgLocation, Loop> mLoopBodies;
	private final LoopDetector<INLOC> mLoopDetector;
	private final IIcfg<OUTLOC> mResult;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final IIcfgSymbolTable mOldSymbolTable;
	private final List<TermVariable> mPathCounter;
	private final Map<TermVariable, TermVariable> mNewPathCounter;

	private final IBacktranslationTracker mBackTranslationTracker;

	public enum DealingWithArraysTypes {
		EXCEPTION, SKIP_LOOP;
	}

	private final DealingWithArraysTypes mDealingWithArrays;

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
			final ITransformulaTransformer transformer, final IUltimateServiceProvider services,
			final DealingWithArraysTypes options) {

		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mBackTranslationTracker = backtranslationTracker;
		mScript = origIcfg.getCfgSmtToolkit().getManagedScript();
		mLogger = Objects.requireNonNull(logger);
		mServices = services;
		mLoopDetector = new LoopDetector<>(mLogger, origIcfg, mScript, mServices);
		mOldSymbolTable = originalIcfg.getCfgSmtToolkit().getSymbolTable();

		mPathCounter = new ArrayList<>();
		mNewPathCounter = new HashMap<>();

		// How to deal with Arrays in the loop:
		mDealingWithArrays = options;

		mLoopBodies = mLoopDetector.getLoopBodies();

		mResult = transform(originalIcfg, funLocFac, backtranslationTracker, outLocationClass, newIcfgIdentifier,
				transformer);
	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer) {

		transformer.preprocessIcfg(originalIcfg);

		for (final Entry<IcfgLocation, Loop> entry : mLoopBodies.entrySet()) {
			if (entry.getValue().getPath().isEmpty()) {
				continue;
			}
			summarizeLoop(entry.getValue());
		}

		final BasicIcfg<OUTLOC> resultIcfg = new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(),
				outLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(funLocFac,
				backtranslationTracker, transformer, originalIcfg, resultIcfg);
		processLocations(originalIcfg.getInitialNodes(), lst);
		lst.finish();

		return resultIcfg;
	}

	private void summarizeLoop(final Loop loop) {

		if (loop.isSummarized()) {
			return;
		}
		final TermClassifier classifier = new TermClassifier();
		classifier.checkTerm(loop.getFormula().getClosedFormula());

		if (classifier.hasArrays() && mDealingWithArrays.equals(DealingWithArraysTypes.EXCEPTION)) {
			mLogger.debug("LOOP HAS ARRAYS");
			throw new IllegalArgumentException("Cannot deal with Arrays");
		}
		if (classifier.hasArrays() && mDealingWithArrays.equals(DealingWithArraysTypes.SKIP_LOOP)) {
			mLogger.debug("LOOP HAS ARRAYS");
			return;
		}

		if (loop.isNested()) {
			for (final Loop nestedLoop : loop.getNestedLoops()) {
				summarizeLoop(nestedLoop);
			}
		}

		for (final Backbone backbone : loop.getBackbones()) {

			final SimultaneousUpdate update = new SimultaneousUpdate(backbone.getFormula(), mScript);

			backbone.setFormula(loop.updateVars(backbone.getFormula(), loop.getInVars(), loop.getOutVars()));
			final UnmodifiableTransFormula tf = (UnmodifiableTransFormula) backbone.getFormula();

			final SymbolicMemory symbolicMemory = new SymbolicMemory(mScript, mServices, mLogger, tf, mOldSymbolTable);
			symbolicMemory.updateVars(update.getUpdatedVars());

			final UnmodifiableTransFormula condition = symbolicMemory
					.updateCondition(TransFormulaUtils.computeGuard(tf, mScript, mServices, mLogger));

			final TermVariable backbonePathCounter = mScript.constructFreshTermVariable("kappa",
					mScript.getScript().sort(SmtSortUtils.INT_SORT));

			mPathCounter.add(backbonePathCounter);
			backbone.setPathCounter(backbonePathCounter);
			backbone.setCondition(condition);

			/**
			 * Dealing with nested loops
			 */
			if (backbone.isNested()) {
				for (final Loop nestedLoop : backbone.getNestedLoops()) {
					if (nestedLoop.getPath().isEmpty() || nestedLoop.getExitConditions().isEmpty()) {
						continue;
					}

					loop.addVar(nestedLoop.getVars());

					final List<UnmodifiableTransFormula> tfs = new ArrayList<>();
					final UnmodifiableTransFormula updated = (UnmodifiableTransFormula) loop
							.updateVars(backbone.getFormula(), loop.getInVars(), loop.getOutVars());
					tfs.add(updated);
					final UnmodifiableTransFormula updatedExit = (UnmodifiableTransFormula) loop
							.updateVars(nestedLoop.getExitConditions().get(0), loop.getInVars(), loop.getOutVars());
					tfs.add(updatedExit);

					final UnmodifiableTransFormula nestedCondition = TransFormulaUtils.sequentialComposition(mLogger,
							mServices, mScript, false, true, false,
							XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
							SimplificationTechnique.SIMPLIFY_DDA, tfs);

					backbone.setCondition(nestedCondition);
					symbolicMemory.updateVars(nestedLoop.getIteratedMemory().getIteratedMemory());
				}
			}
			backbone.setSymbolicMemory(symbolicMemory);
		}

		for (int i = 0; i < mPathCounter.size(); i++) {
			final TermVariable newBackbonePathCounter = mScript.constructFreshTermVariable("tau",
					mScript.getScript().sort(SmtSortUtils.INT_SORT));
			mNewPathCounter.put(mPathCounter.get(i), newBackbonePathCounter);
		}
		loop.addVar(mPathCounter);
		final List<TermVariable> newPathCounterVals = new ArrayList<>(mNewPathCounter.values());
		loop.addVar(newPathCounterVals);

		final List<TermVariable> pathCounters = new ArrayList<>(mPathCounter);
		final IteratedSymbolicMemory iteratedSymbolicMemory = new IteratedSymbolicMemory(mScript, mServices, mLogger,
				loop, pathCounters, mNewPathCounter);

		iteratedSymbolicMemory.updateMemory();
		iteratedSymbolicMemory.updateCondition();

		Term loopSummary = iteratedSymbolicMemory.getAbstractCondition();

		loop.setCondition(loopSummary);

		loop.setIteratedSymbolicMemory(iteratedSymbolicMemory);

		TransFormulaBuilder tfb = new TransFormulaBuilder(loop.getInVars(), loop.getOutVars(), true, null, true, null,
				false);

		tfb.setFormula(loopSummary);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		tfb.addAuxVarsButRenameToFreshCopies(mNewPathCounter.keySet(), mScript);

		UnmodifiableTransFormula acceleratedLoopSummary = tfb.finishConstruction(mScript);

		for (final IcfgEdge exitTransition : loop.getExitTransitions()) {
			final UnmodifiableTransFormula exit = TransFormulaUtils.sequentialComposition(mLogger, mServices, mScript,
					true, true, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
					SimplificationTechnique.SIMPLIFY_DDA,
					Arrays.asList(acceleratedLoopSummary, exitTransition.getTransformula()));
			loop.addExitCondition(exit);
		}

		/**
		 * Dealing with Errorpaths in loop
		 */
		for (final Entry<IcfgLocation, Backbone> errorPath : loop.getErrorPaths().entrySet()) {

			final TransFormula errorTf = loop.updateVars(errorPath.getValue().getFormula(), loop.getInVars(),
					loop.getOutVars());
			Term errorTerm = iteratedSymbolicMemory.updateBackboneTerm(errorTf);

			for (final TermVariable pathCounter : mPathCounter) {
				final Term t = mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)), pathCounter);
				errorTerm = mScript.getScript().term("and", t, errorTerm);
			}

			errorTerm = mScript.getScript().quantifier(QuantifiedFormula.EXISTS,
					mPathCounter.toArray(new TermVariable[mPathCounter.size()]), errorTerm);

			TransFormulaBuilder tfb1 = new TransFormulaBuilder(loop.getInVars(), loop.getOutVars(), true, null, true,
					null, true);

			tfb1.setFormula(PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript, errorTerm,
					SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION));

			tfb1.setInfeasibility(Infeasibility.NOT_DETERMINED);

			final Backbone newErrorPath = new Backbone(errorPath.getValue().getPath(), tfb1.finishConstruction(mScript),
					false, null);
			loop.replaceErrorPath(errorPath.getKey(), newErrorPath);

		}
		mLogger.debug("LOOP SUMMARY: " + loop.getExitConditions());
		loop.setSummarized();
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

			if (mLoopBodies.containsKey(oldSource) && mLoopBodies.get(oldSource).getIteratedMemory() != null) {
				final Loop loop = mLoopBodies.get(oldSource);

				if (!loop.getErrorPaths().isEmpty()) {
					mLogger.debug("LOOP WITH ERRORPATH");

					for (final Entry<IcfgLocation, Backbone> entry : loop.getErrorPaths().entrySet()) {
						final OUTLOC newTarget = lst.createNewLocation((INLOC) entry.getKey());

						lst.createNewInternalTransition(newSource, newTarget,
								(UnmodifiableTransFormula) entry.getValue().getFormula(), true);
					}
				}

				for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {

					if (loop.getLoopExit().equals(oldTransition.getTarget())) {
						final INLOC oldTarget = (INLOC) oldTransition.getTarget();
						open.add(oldTarget);
						continue;
					}

					if (loop.getPath().contains(oldTransition)) {

						final OUTLOC loopExit = lst.createNewLocation((INLOC) loop.getLoopExit());
						for (UnmodifiableTransFormula exitTransition : loop.getExitConditions()) {
							final IcfgEdge newTransition = lst.createNewInternalTransition(newSource, loopExit,
									exitTransition, true);
							mBackTranslationTracker.rememberRelation(oldTransition, newTransition);
						}

					} else {
						final INLOC oldTarget = (INLOC) oldTransition.getTarget();
						open.add(oldTarget);
						final OUTLOC newTarget = lst.createNewLocation(oldTarget);
						lst.createNewTransition(newSource, newTarget, oldTransition);
					}
				}

			} else {
				for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
					final INLOC oldTarget = (INLOC) oldTransition.getTarget();
					open.add(oldTarget);
					final OUTLOC newTarget = lst.createNewLocation(oldTarget);
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}
	}

	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}
