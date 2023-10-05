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
package de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.BvToIntTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformationBacktranslator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformerSequence;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.LocalTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.MapEliminationTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.SifaSimplifierTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.HeapSepIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.CopyingTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach.IcfgLoopAcceleration;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach.IcfgLoopAcceleration.LoopAccelerationOptions;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRTransformer.FastUPRReplacementMethod;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAccelerationIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.mohr.IcfgLoopTransformerMohr;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.QvasrIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasrs.QvasrsIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.WernerLoopAccelerationIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.WernerLoopAccelerationIcfgTransformer.DealingWithArraysTypes;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.woelfing.LoopAccelerationIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.mapelim.monniaux.MonniauxMapEliminator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.DNF;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.ModuloNeighborTransformation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteIte;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.SimplifyPreprocessor;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TransitionPreprocessor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.DefaultEqualityAnalysisProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination.MapEliminationSettings;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.IntToBvBackTranslation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation.preferences.IcfgTransformationPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation.preferences.IcfgTransformationPreferences.TransformationTestType;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgTransformationObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IcfgTransformationBacktranslator mBacktranslator;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;

	private IIcfg<?> mResult;

	public IcfgTransformationObserver(final ILogger logger, final IUltimateServiceProvider services,
			final IcfgTransformationBacktranslator backtranslator, final SimplificationTechnique simplTech,
			final XnfConversionTechnique xnfConvTech) {
		mLogger = logger;
		mServices = services;
		mBacktranslator = backtranslator;
		mSimplificationTechnique = simplTech;
		mXnfConversionTechnique = xnfConvTech;
		mResult = null;
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
		if (root instanceof IIcfg) {
			processIcfg((IIcfg<?>) root);
			return false;
		}
		return true;
	}

	@SuppressWarnings("unchecked")
	private <INLOC extends IcfgLocation> void processIcfg(final IIcfg<INLOC> icfg) {
		final IcfgTransformationBacktranslator backtranslationTracker = mBacktranslator;

		if (icfg.getLocationClass().equals(BoogieIcfgLocation.class)) {
			mResult = createTransformer((IIcfg<BoogieIcfgLocation>) icfg, createBoogieLocationFactory(),
					BoogieIcfgLocation.class, backtranslationTracker);
		} else {
			mResult = createTransformer(icfg, createIcfgLocationFactory(), IcfgLocation.class, backtranslationTracker);
		}
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> createTransformer(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker) {

		// TODO: Decide which transformer should be used via settings (and/or
		// allow chaining of transformers in
		// icfgtransformer
		final ReplacementVarFactory fac = new ReplacementVarFactory(icfg.getCfgSmtToolkit(), false);

		final IPreferenceProvider ups = IcfgTransformationPreferences.getPreferenceProvider(mServices);
		final TransformationTestType transformation =
				ups.getEnum(IcfgTransformationPreferences.LABEL_TRANSFORMATION_TYPE, TransformationTestType.class);

		mLogger.info("Applying ICFG transformation %s", transformation);
		switch (transformation) {
		case HEAP_SEPARATOR:
			return applyHeapSeparator(icfg, locFac, outlocClass, backtranslationTracker, fac, mServices,
					new AbsIntEqualityProvider(mServices));
		case LOOP_ACCELERATION_EXAMPLE:
			return applyLoopAccelerationEx(icfg, locFac, outlocClass, backtranslationTracker);
		case LOOP_ACCELERATION_BIESENBACH:
			return applyLoopAccelerationBiesenbach(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_JORDAN:
			return applyLoopAccelerationJordan(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_QVASR:
			return applyLoopAccelerationQvasr(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_QVASRS:
			return applyLoopAccelerationQvasrs(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_MOHR:
			return applyLoopAccelerationMohr(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_WOELFING:
			return applyLoopAccelerationWoelfing(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_FASTUPR:
			return applyLoopAccelerationFastUPR(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_WERNER:
			return applyLoopAccelerationWerner(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case MAP_ELIMINATION_NO_EQUALITY:
			return applyMapElimination(icfg, locFac, outlocClass, backtranslationTracker, fac,
					new DefaultEqualityAnalysisProvider<>());
		case MAP_ELIMINATION_EQUALITY:
			return applyMapElimination(icfg, locFac, outlocClass, backtranslationTracker, fac,
					new AbsIntEqualityProvider(mServices));
		case REMOVE_DIV_MOD:
			return applyRemoveDivMod(mLogger, icfg, locFac, outlocClass, backtranslationTracker, fac);
		case MODULO_NEIGHBOR:
			return applyModuloNeighbor(mLogger, icfg, locFac, outlocClass, backtranslationTracker, fac, mServices);
		case BV_TO_INT_SUM:
			return applyBvToIntTranslation(mLogger, icfg, locFac, outlocClass, backtranslationTracker, mServices,
					ConstraintsForBitwiseOperations.SUM);
		case BV_TO_INT_BITWISE:
			return applyBvToIntTranslation(mLogger, icfg, locFac, outlocClass, backtranslationTracker, mServices,
					ConstraintsForBitwiseOperations.BITWISE);
		case BV_TO_INT_LAZY:
			return applyBvToIntTranslation(mLogger, icfg, locFac, outlocClass, backtranslationTracker, mServices,
					ConstraintsForBitwiseOperations.LAZY);
		case BV_TO_INT_NONE:
			return applyBvToIntTranslation(mLogger, icfg, locFac, outlocClass, backtranslationTracker, mServices,
					ConstraintsForBitwiseOperations.NONE);
		case MAP_ELIMINATION_MONNIAUX:
			return (IIcfg<OUTLOC>) applyMapEliminationMonniaux((IIcfg<IcfgLocation>) icfg, backtranslationTracker);
		case SIFA_SIMPLIFICATION:
			return applySifaSimplification(icfg, locFac, outlocClass, backtranslationTracker);
		default:
			throw new UnsupportedOperationException("Unknown transformation type: " + transformation);
		}
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyHeapSeparator(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac,
			final IUltimateServiceProvider services,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {

		/**
		 * name of the valid array, copied from class "SFO" in C to Boogie translation
		 */
		final String VALID = "#valid";

		// equalityProvider.setTrackedArrays(Arrays.asList(new String[]{ VALID, MEMORY } ));

		IProgramNonOldVar validArray = null;
		for (final IProgramNonOldVar global : icfg.getCfgSmtToolkit().getSymbolTable().getGlobals()) {
			if (global.getGloballyUniqueId().equals(VALID)) {
				validArray = global;
				break;
			}
		}
		if (validArray == null) {
			mLogger.warn("HeapSeparator: input icfg has no '#valid' array -- returning unchanged Icfg!");
			return new IcfgTransformer<>(mLogger, icfg, locFac, backtranslationTracker, outlocClass,
					icfg.getIdentifier() + "left_unchanged_by_heapseparator",
					new IdentityTransformer(icfg.getCfgSmtToolkit())).getResult();
		}

		final HeapSepIcfgTransformer<INLOC, OUTLOC> icfgTransformer =
				new HeapSepIcfgTransformer<>(mLogger, mServices, icfg, locFac, fac, backtranslationTracker, outlocClass,
						"heap_separated_icfg", equalityProvider, validArray);

		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new StatisticsResult<>(Activator.PLUGIN_ID, "Abstract Interpretation statistics",
						((AbsIntEqualityProvider) equalityProvider).getAbsIntBenchmark()));

		mServices.getResultService().reportResult(Activator.PLUGIN_ID, new StatisticsResult<>(Activator.PLUGIN_ID,
				"HeapSeparatorStatistics", icfgTransformer.getStatistics()));

		return icfgTransformer.getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationMohr(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac) {
		return new IcfgLoopTransformerMohr<>(mLogger, mServices, icfg, locFac, backtranslationTracker, outlocClass,
				"IcfgWithLoopAccelerationMohr").getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationWoelfing(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac) {
		return new LoopAccelerationIcfgTransformer<>(mLogger, icfg, locFac, backtranslationTracker, outlocClass,
				"IcfgWithLoopAccelerationWoelfing", mServices).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationBiesenbach(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac) {
		final LoopAccelerationOptions options = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(IcfgTransformationPreferences.LABEL_LA_BB_MODE, LoopAccelerationOptions.class);
		return new IcfgLoopAcceleration<>(mLogger, icfg, outlocClass, locFac, icfg.getIdentifier() + "IcfgDuplicate",
				backtranslationTracker, mServices, options).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationJordan(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac) {
		return new JordanLoopAccelerationIcfgTransformer<>(mLogger, icfg, outlocClass, locFac,
				icfg.getIdentifier() + "Jordan", backtranslationTracker, mServices).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationQvasr(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac) {
		return new QvasrIcfgTransformer<>(mLogger, icfg, outlocClass, locFac, icfg.getIdentifier() + "qvasr",
				backtranslationTracker, mServices).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationQvasrs(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac) {
		final ITransformulaTransformer transformer = new CopyingTransformulaTransformer(mLogger,
				icfg.getCfgSmtToolkit().getManagedScript(), icfg.getCfgSmtToolkit());
		return new QvasrsIcfgTransformer<>(mLogger, icfg, outlocClass, locFac,
				icfg.getIdentifier() + "qvasrs transformation", transformer, backtranslationTracker, mServices)
						.getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationFastUPR(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac) {
		final FastUPRReplacementMethod replacementMetho = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(IcfgTransformationPreferences.LABEL_FASTUPR_MODE, FastUPRReplacementMethod.class);
		return new FastUPRTransformer<>(mLogger, icfg, outlocClass, locFac, icfg.getIdentifier() + "FastUPR",
				backtranslationTracker, mServices, replacementMetho).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationWerner(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac) {
		final DealingWithArraysTypes options = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(IcfgTransformationPreferences.LABEL_LA_WERNER_MODE, DealingWithArraysTypes.class);
		return new WernerLoopAccelerationIcfgTransformer<>(mLogger, icfg, locFac, backtranslationTracker, outlocClass,
				icfg.getIdentifier() + "IcfgDuplicate", mServices, options, 10).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationEx(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker) {
		final ITransformulaTransformer transformer = new CopyingTransformulaTransformer(mLogger,
				icfg.getCfgSmtToolkit().getManagedScript(), icfg.getCfgSmtToolkit());
		return new IcfgTransformer<>(mLogger, icfg, locFac, backtranslationTracker, outlocClass,
				icfg.getIdentifier() + "IcfgDuplicate", transformer).getResult();
	}

	private static <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyRemoveDivMod(
			final ILogger logger, final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac,
			final Class<OUTLOC> outlocClass, final IcfgTransformationBacktranslator backtranslationTracker,
			final ReplacementVarFactory fac) {
		final ITransformulaTransformer transformer =
				new LocalTransformer(new RewriteDivision(fac), icfg.getCfgSmtToolkit().getManagedScript(), fac);
		final IcfgTransformer<INLOC, OUTLOC> icfgTransformer = new IcfgTransformer<>(logger, icfg, locFac,
				backtranslationTracker, outlocClass, icfg.getIdentifier() + "TransformedIcfg", transformer);
		return icfgTransformer.getResult();
	}

	private static <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyModuloNeighbor(
			final ILogger logger, final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac,
			final Class<OUTLOC> outlocClass, final IcfgTransformationBacktranslator backtranslationTracker,
			final ReplacementVarFactory fac, final IUltimateServiceProvider services) {
		final List<TransitionPreprocessor> transitionPreprocessors = new ArrayList<>();
		transitionPreprocessors.add(new RewriteIte());
		transitionPreprocessors.add(new SimplifyPreprocessor(services, SimplificationTechnique.SIMPLIFY_QUICK));
		transitionPreprocessors.add(new ModuloNeighborTransformation(services, true));
		transitionPreprocessors.add(new DNF(services, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION));

		final ITransformulaTransformer transformer =
				new LocalTransformer(transitionPreprocessors, icfg.getCfgSmtToolkit().getManagedScript(), fac);
		final IcfgTransformer<INLOC, OUTLOC> icfgTransformer = new IcfgTransformer<>(logger, icfg, locFac,
				backtranslationTracker, outlocClass, icfg.getIdentifier() + "TransformedIcfg", transformer);
		return icfgTransformer.getResult();
	}

	private static <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyBvToIntTranslation(
			final ILogger logger, final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac,
			final Class<OUTLOC> outlocClass, final IcfgTransformationBacktranslator backtranslationTracker,
			final IUltimateServiceProvider services, final ConstraintsForBitwiseOperations cfbo) {
		final IPreferenceProvider ups = services.getPreferenceProvider(Activator.PLUGIN_ID);

		final BvToIntTransformulaTransformer transformer = new BvToIntTransformulaTransformer(icfg.getCfgSmtToolkit().getManagedScript(), cfbo,
				ups.getBoolean(IcfgTransformationPreferences.LABEL_NUTZ_TRANSFORMATION));
		final IcfgTransformer<INLOC, OUTLOC> icfgTransformer = new IcfgTransformer<>(logger, icfg, locFac,
				backtranslationTracker, outlocClass, icfg.getIdentifier() + "TransformedIcfg", transformer);
		final UnaryOperator<Term> backtranslation =
				x -> new IntToBvBackTranslation(icfg.getCfgSmtToolkit().getManagedScript(),
						new LinkedHashMap<>(transformer.getBacktranslationMap()), Collections.emptySet(), null)
								.transform(x);

		backtranslationTracker.addExpressionBacktranslation(backtranslation);

		return icfgTransformer.getResult();
	}

	@SuppressWarnings("unchecked")
	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyMapElimination(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker, final ReplacementVarFactory fac,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {

		final List<ITransformulaTransformer> transformers = new ArrayList<>();
		transformers.add(new LocalTransformer(new DNF(mServices, mXnfConversionTechnique),
				icfg.getCfgSmtToolkit().getManagedScript(), fac));
		final MapEliminationSettings settings = getMapElimSettings();
		transformers.add(new MapEliminationTransformer(mServices, mLogger, icfg.getCfgSmtToolkit().getManagedScript(),
				icfg.getCfgSmtToolkit().getSymbolTable(), fac, settings, equalityProvider));
		return new IcfgTransformerSequence<>(mLogger, icfg, locFac, (ILocationFactory<OUTLOC, OUTLOC>) locFac,
				backtranslationTracker, outlocClass, icfg.getIdentifier() + "IcfgWithMapElim", transformers)
						.getResult();
	}

	private IIcfg<IcfgLocation> applyMapEliminationMonniaux(final IIcfg<IcfgLocation> icfg,
			final IcfgTransformationBacktranslator backtranslationTracker) {
		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final int numberOfCells = ups.getInt(IcfgTransformationPreferences.LABEL_MAPELIM_MONNIAUX_NUMBER_OF_CELLS);
		return new MonniauxMapEliminator(mServices, mLogger, icfg, backtranslationTracker, numberOfCells).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applySifaSimplification(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IcfgTransformationBacktranslator backtranslationTracker) {
		final SifaSimplifierTransformer transformer = new SifaSimplifierTransformer(mServices, icfg.getCfgSmtToolkit());
		backtranslationTracker.addExpressionBacktranslation(transformer::backtranslate);
		return new IcfgTransformer<>(mLogger, icfg, locFac, backtranslationTracker, outlocClass,
				icfg.getIdentifier() + "_simplified", transformer).getResult();
	}

	private MapEliminationSettings getMapElimSettings() {
		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final boolean addInequalities = ups.getBoolean(IcfgTransformationPreferences.LABEL_MAPELIM_ADD_INEQUALITIES);
		final boolean onlyTrivialImplicationsForModifiedArguments = ups
				.getBoolean(IcfgTransformationPreferences.LABEL_MAPELIM_ONLY_TRIVIAL_IMPLICATIONS_MODIFIED_ARGUMENTS);
		final boolean onlyTrivialImplicationsArrayWrite =
				ups.getBoolean(IcfgTransformationPreferences.LABEL_MAPELIM_ONLY_TRIVIAL_IMPLICATIONS_ARRAY_WRITE);
		final boolean onlyArgumentsInFormula =
				ups.getBoolean(IcfgTransformationPreferences.LABEL_MAPELIM_ONLY_ARGUMENTS_IN_FORMULA);
		return new MapEliminationSettings(addInequalities, onlyTrivialImplicationsForModifiedArguments,
				onlyTrivialImplicationsArrayWrite, onlyArgumentsInFormula, mSimplificationTechnique,
				mXnfConversionTechnique);
	}

	private static ILocationFactory<BoogieIcfgLocation, BoogieIcfgLocation> createBoogieLocationFactory() {
		return (oldLocation, debugIdentifier, procedure) -> {
			final BoogieIcfgLocation rtr = new BoogieIcfgLocation(debugIdentifier, procedure,
					oldLocation.isErrorLocation(), oldLocation.getBoogieASTNode());
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};
	}

	@SuppressWarnings("unchecked")
	private static <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> ILocationFactory<INLOC, OUTLOC>
			createIcfgLocationFactory() {
		return (oldLocation, debugIdentifier, procedure) -> {
			final IcfgLocation rtr = new IcfgLocation(debugIdentifier, procedure);
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return (OUTLOC) rtr;
		};
	}

}
