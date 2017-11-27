
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

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

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
	private final Map<IcfgLocation, Boolean> mOverApproximation;

	private final IBacktranslationTracker mBackTranslationTracker;

	/**
	 * How to deal with arrays, either throw an exception or skip the loop
	 * entirely
	 * 
	 * @author Jonas Werner (jonaswerner95@gmail.com)
	 *
	 */
	public enum DealingWithArraysTypes {
		EXCEPTION, SKIP_LOOP;
	}

	private final DealingWithArraysTypes mDealingWithArrays;

	/**
	 * Construct a new Loop Accelerator
	 * 
	 * @param logger
	 *            An {@link ILogger}
	 * @param originalIcfg
	 *            The original Icfg
	 * @param funLocFac
	 * @param backtranslationTracker
	 * @param outLocationClass
	 * @param newIcfgIdentifier
	 * @param transformer
	 * @param services
	 * @param options
	 *            how to deal with Arrays
	 * @param backboneLimit
	 *            maximum number of backbones
	 */
	public WernerLoopAccelerationIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IUltimateServiceProvider services,
			final DealingWithArraysTypes options, final int backboneLimit) {

		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mBackTranslationTracker = backtranslationTracker;
		mScript = origIcfg.getCfgSmtToolkit().getManagedScript();
		mLogger = Objects.requireNonNull(logger);
		mServices = services;
		mLoopDetector = new LoopDetector<>(mLogger, origIcfg, mScript, mServices, backboneLimit);
		mOldSymbolTable = originalIcfg.getCfgSmtToolkit().getSymbolTable();

		mPathCounter = new ArrayList<>();
		mNewPathCounter = new HashMap<>();
		mOverApproximation = new HashMap<>();

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

		mPathCounter.clear();
		mNewPathCounter.clear();

		if (loop.isSummarized() || SmtUtils.isTrue(loop.getFormula().getFormula())
				|| SmtUtils.isFalse(loop.getFormula().getFormula())) {
			return;
		}
		final TermClassifier classifier = new TermClassifier();
		classifier.checkTerm(loop.getFormula().getClosedFormula());

		/**
		 * Dealing with arrays, decided by mDealingWithArrays
		 */
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
				mOverApproximation.put(nestedLoop.getLoophead(), true);
				summarizeLoop(nestedLoop);
			}
			mOverApproximation.put(loop.getLoophead(), true);
		}

		/**
		 * Go through each backbone and calculate an iterated value
		 */
		for (final Backbone backbone : loop.getBackbones()) {

			final SimultaneousUpdate update = new SimultaneousUpdate(backbone.getFormula(), mScript);

			if (!update.getHavocedVars().isEmpty() || loop.isNested()) {
				mOverApproximation.put(loop.getLoophead(), true);
			}

			backbone.setFormula(loop.updateVars(backbone.getFormula(), loop.getInVars(), loop.getOutVars()));
			final UnmodifiableTransFormula tf = (UnmodifiableTransFormula) backbone.getFormula();

			final SymbolicMemory symbolicMemory = new SymbolicMemory(mScript, mServices, tf, mOldSymbolTable);
			symbolicMemory.updateVars(update.getUpdatedVars());

			final UnmodifiableTransFormula condition = symbolicMemory
					.updateCondition(TransFormulaUtils.computeGuard(tf, mScript, mServices, mLogger));

			final TermVariable backbonePathCounter = mScript.constructFreshTermVariable("kappa",
					mScript.getScript().sort(SmtSortUtils.INT_SORT));

			mPathCounter.add(backbonePathCounter);
			backbone.setPathCounter(backbonePathCounter);
			backbone.setCondition(condition);

			/**
			 * First accelerate each nested loop
			 */
			if (backbone.isNested()) {
				for (final Loop nestedLoop : backbone.getNestedLoops()) {
					if (nestedLoop.getPath().isEmpty() || nestedLoop.getExitConditions().isEmpty()) {
						continue;
					}
					symbolicMemory.updateVars(nestedLoop.getIteratedMemory().getIteratedMemory());
					loop.addVar(nestedLoop.getVars());
					final Map<IProgramVar, TermVariable> oldInvars = loop.getInVars();
					oldInvars.putAll(nestedLoop.getInVars());
					loop.setInVars(oldInvars);
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

		/**
		 * Dealing with nested loops
		 */
		if (loop.isNested()) {
			for (final Loop nestedLoop : loop.getNestedLoops()) {
				loopSummary = SmtUtils.or(mScript.getScript(),
						Arrays.asList(loopSummary, nestedLoop.getExitConditions().get(0).getFormula()));
				final ArrayList<TermVariable> newAuxVars = new ArrayList<>(
						nestedLoop.getExitConditions().get(0).getAuxVars());
				loop.addVar(newAuxVars);
				final Map<IProgramVar, TermVariable> oldOutVars = loop.getOutVars();
				for (final Entry<IProgramVar, TermVariable> outVarNested : nestedLoop.getOutVars().entrySet()) {
					oldOutVars.replace(outVarNested.getKey(), outVarNested.getValue());
				}
			}
		}

		loop.setCondition(loopSummary);
		loop.setIteratedSymbolicMemory(iteratedSymbolicMemory);

		/**
		 * compute the main accelerated loop exit, by combining an exit transition with the loop summary
		 */
		final IcfgEdge exitTransition = loop.getExitTransitions().get(0);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(loop.getInVars(), loop.getOutVars(), true, null, true,
				null, false);

		final TransFormula exit = loop.updateVars(exitTransition.getTransformula(), loop.getInVars(),
				loop.getOutVars());

		final Term exitTerm = SmtUtils.and(mScript.getScript(), Arrays.asList(loopSummary, exit.getFormula()));
		tfb.setFormula(exitTerm);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		final Set<TermVariable> auxVars = new HashSet<>(loop.getVars());
		tfb.addAuxVarsButRenameToFreshCopies(auxVars, mScript);
		final UnmodifiableTransFormula exitFormula = tfb.finishConstruction(mScript);

		/**
		 * accelerated loop
		 */
		loop.addExitCondition(exitFormula);

		/**
		 * Dealing with breaks
		 */
		for (final UnmodifiableTransFormula breakTf : loop.getBreakFormulas()) {

			final TransFormulaBuilder builder = new TransFormulaBuilder(loop.getInVars(), loop.getOutVars(), true, null,
					true, null, false);

			final TransFormula breakFormula = loop.updateVars(breakTf, loop.getInVars(), loop.getOutVars());

			final Term breakTerm = SmtUtils.and(mScript.getScript(),
					Arrays.asList(loopSummary, breakFormula.getFormula()));
			builder.setFormula(breakTerm);
			builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
			final Set<TermVariable> breakVars = new HashSet<>(loop.getVars());
			builder.addAuxVarsButRenameToFreshCopies(breakVars, mScript);
			final UnmodifiableTransFormula breakFormulaDone = builder.finishConstruction(mScript);
			loop.addExitCondition(breakFormulaDone);

		}

		/**
		 * Dealing with Errorpaths in loop
		 */
		for (final Entry<IcfgLocation, Backbone> errorPath : loop.getErrorPaths().entrySet()) {

			final TransFormulaBuilder builder = new TransFormulaBuilder(loop.getInVars(), loop.getOutVars(), true, null,
					true, null, false);

			final TransFormula errorFormula = loop.updateVars(errorPath.getValue().getFormula(), loop.getInVars(),
					loop.getOutVars());

			final Term errorTerm = SmtUtils.or(mScript.getScript(),
					Arrays.asList(loopSummary, errorFormula.getFormula()));
			builder.setFormula(errorTerm);
			builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
			final Set<TermVariable> errorVars = new HashSet<>(loop.getVars());
			builder.addAuxVarsButRenameToFreshCopies(errorVars, mScript);
			final UnmodifiableTransFormula errorFormulaDone = builder.finishConstruction(mScript);
			final Backbone newErrorPath = new Backbone(errorPath.getValue().getPath(), errorFormulaDone, false, null);
			loop.replaceErrorPath(errorPath.getKey(), newErrorPath);

		}

		if (!mOverApproximation.containsKey(loop.getLoophead())) {
			mOverApproximation.put(loop.getLoophead(), false);
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

			final Set<Triple<OUTLOC, OUTLOC, IIcfgReturnTransition<?, ?>>> returnTransitions = new HashSet<>();

			/**
			 * Add accelerated loop
			 */
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
									exitTransition, mOverApproximation.get(newSource));
							new Overapprox("loop acceleration", null).annotate(newTransition);
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

					if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
						returnTransitions
								.add(new Triple<>(newSource, newTarget, (IIcfgReturnTransition<?, ?>) oldTransition));
					} else {
						lst.createNewTransition(newSource, newTarget, oldTransition);
					}
				}
			}
			returnTransitions.stream().filter(a -> lst.isCorrespondingCallContained(a.getThird()))
					.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), (IcfgEdge) a.getThird()));
		}
	}

	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}
