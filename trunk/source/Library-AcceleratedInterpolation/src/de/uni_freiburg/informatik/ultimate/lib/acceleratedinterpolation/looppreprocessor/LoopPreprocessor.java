/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.PredicateHelper;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;

/**
 * Preprocess a given loop by transforming not supported transitions.
 *
 * @author Jonas Werner <wernerj@informatik.uni-freiburg.de>
 *
 * @param <LETTER>
 *            transition type
 */
public class LoopPreprocessor<L extends IIcfgTransition<?>>
		implements ILoopPreprocessor<IcfgLocation, L, UnmodifiableTransFormula> {

	private final ManagedScript mScript;
	private final ILogger mLogger;
	// private final IPredicateUnifier mPredUnifier;
	private final PredicateHelper<L> mPredHelper;
	private final IUltimateServiceProvider mServices;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final CfgSmtToolkit mCsToolkit;
	private final List<String> mOptions;

	/**
	 * Remove for example modulo operations from a loop, because FastUPR does not support it.
	 *
	 * @param logger
	 * @param script
	 * @param predUnifier
	 */
	public LoopPreprocessor(final ILogger logger, final ManagedScript script, final IUltimateServiceProvider services,
			final IPredicateUnifier predUnifier, final PredicateHelper<L> predHelper, final CfgSmtToolkit toolkit,
			final List<String> preProcessOptions) {
		mLogger = logger;
		mScript = script;
		// mPredUnifier = predUnifier;
		mPredHelper = predHelper;
		mServices = services;
		mCsToolkit = toolkit;
		mReplacementVarFactory = new ReplacementVarFactory(mCsToolkit, false);
		mOptions = preProcessOptions;
	}

	@Override
	public Map<IcfgLocation, List<UnmodifiableTransFormula>>
			preProcessLoopInterprocedual(final Map<IcfgLocation, Set<List<L>>> loop) {

		final Map<IcfgLocation, List<UnmodifiableTransFormula>> result = new HashMap<>();
		for (final Entry<IcfgLocation, Set<List<L>>> loopSet : loop.entrySet()) {
			final IcfgLocation loophead = loopSet.getKey();
			if (loopSet.getValue() == null) {
				continue;
			}
			boolean noSplit = false;
			final List<UnmodifiableTransFormula> disjuncts = new ArrayList<>();
			for (final List<L> loopActions : loopSet.getValue()) {
				UnmodifiableTransFormula interprocedualTransformula = SequentialComposition
						.getInterproceduralTransFormula(mCsToolkit, false, false, false, false, mLogger, mServices,
								loopActions, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
								SimplificationTechnique.SIMPLIFY_DDA);
				for (final String option : mOptions) {
					final ApplicationTermFinder applicationTermFinder = new ApplicationTermFinder(option, false);
					if (!applicationTermFinder.findMatchingSubterms(interprocedualTransformula.getFormula())
							.isEmpty()) {
						interprocedualTransformula = preProcessing(option, interprocedualTransformula);
					}
					if ("No DNF".equals(option)) {
						noSplit = true;
					}
					mLogger.debug("Preprocess");
				}
				final ModifiableTransFormula modTf = ModifiableTransFormulaUtils
						.buildTransFormula(interprocedualTransformula, mReplacementVarFactory, mScript);
				if (noSplit) {
					disjuncts.add(interprocedualTransformula);
				} else {
					disjuncts.addAll(
							LoopPreprocessorTransformulaTransformer.splitDisjunction(modTf, mScript, mServices));
				}
			}
			if (noSplit) {
				final UnmodifiableTransFormula[] tfs =
						disjuncts.toArray(new UnmodifiableTransFormula[disjuncts.size()]);
				final UnmodifiableTransFormula disjunct = TransFormulaUtils.parallelComposition(mLogger, mServices,
						mScript, null, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, false, tfs);
				final ArrayList<UnmodifiableTransFormula> dj = new ArrayList<>();
				dj.add(disjunct);
				result.put(loophead, dj);
			} else {
				result.put(loophead, disjuncts);
			}
			mLogger.debug("Loop preprocessed");
		}
		return result;
	}

	/**
	 * Preprocess a loop to remove unsupported operations, such as modulo
	 */
	@Override
	public Map<IcfgLocation, List<UnmodifiableTransFormula>>
			preProcessLoop(final Map<IcfgLocation, Set<List<L>>> loop) {
		final Map<IcfgLocation, List<UnmodifiableTransFormula>> result = new HashMap<>();
		for (final Entry<IcfgLocation, Set<List<L>>> loopSet : loop.entrySet()) {
			final IcfgLocation loophead = loopSet.getKey();
			if (loopSet.getValue() == null) {
				continue;
			}
			final List<UnmodifiableTransFormula> disjuncts = new ArrayList<>();
			for (final List<L> loopActions : loopSet.getValue()) {
				final List<UnmodifiableTransFormula> loopTransitions = convertActionToFormula(loopActions);
				UnmodifiableTransFormula loopRelation = TransFormulaUtils.sequentialComposition(mLogger, mServices,
						mScript, true, true, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
						SimplificationTechnique.SIMPLIFY_DDA, loopTransitions);
				/*
				 * Transform found unsupported operations:
				 */
				boolean noSplit = false;
				for (final String option : mOptions) {
					final ApplicationTermFinder applicationTermFinder = new ApplicationTermFinder(option, false);
					if (!applicationTermFinder.findMatchingSubterms(loopRelation.getFormula()).isEmpty()) {
						loopRelation = preProcessing(option, loopRelation);
					}
					if ("no DNF".equals(option)) {
						noSplit = true;
					}
					mLogger.debug("Preprocess");
				}
				final ModifiableTransFormula modTf =
						ModifiableTransFormulaUtils.buildTransFormula(loopRelation, mReplacementVarFactory, mScript);
				if (noSplit) {
					disjuncts.add(loopRelation);
				} else {
					disjuncts.addAll(
							LoopPreprocessorTransformulaTransformer.splitDisjunction(modTf, mScript, mServices));
				}
			}
			result.put(loophead, disjuncts);
			mLogger.debug("Loop preprocessed");
		}
		return result;
	}

	private UnmodifiableTransFormula preProcessing(final String option, final UnmodifiableTransFormula loopRelation) {
		final ModifiableTransFormula modTf =
				ModifiableTransFormulaUtils.buildTransFormula(loopRelation, mReplacementVarFactory, mScript);
		switch (option) {
		case "mod":
			return LoopPreprocessorTransformulaTransformer.moduloTransformation(modTf, mScript, mReplacementVarFactory,
					mServices);
		case "not":
			return LoopPreprocessorTransformulaTransformer.notTransformation(modTf, mScript);
		case "div":
			return LoopPreprocessorTransformulaTransformer.divisionTransformation(modTf, mScript,
					mReplacementVarFactory);
		case "ite":
			return LoopPreprocessorTransformulaTransformer.iteTransformation(modTf, mScript);
		default:
			break;
		}
		return loopRelation;
	}

	private List<UnmodifiableTransFormula> convertActionToFormula(final List<L> actions) {
		final List<UnmodifiableTransFormula> tfs = new ArrayList<>();
		for (final L action : actions) {
			tfs.add(action.getTransformula());
		}
		return tfs;
	}
}