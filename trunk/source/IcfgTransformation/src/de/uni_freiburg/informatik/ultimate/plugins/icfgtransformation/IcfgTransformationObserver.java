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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformerSequence;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.LocalTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.MapEliminationTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.ExampleLoopAccelerationTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach.LoopDetectionBB;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.woelfing.LoopAccelerationIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.DNF;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.DefaultEqualityAnalysisProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminationSettings;
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
		final IBacktranslationTracker backtranslationTracker = (oldTransition, newTransition) -> mBacktranslator
				.mapEdges((IcfgEdge) newTransition, (IcfgEdge) oldTransition);

		if (icfg.getLocationClass().equals(BoogieIcfgLocation.class)) {
			mResult = createTransformer((IIcfg<BoogieIcfgLocation>) icfg, createBoogieLocationFactory(),
					BoogieIcfgLocation.class, backtranslationTracker);
		} else {
			mResult = createTransformer(icfg, createIcfgLocationFactory(), IcfgLocation.class, backtranslationTracker);
		}
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> createTransformer(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IBacktranslationTracker backtranslationTracker) {

		// TODO: Decide which transformer should be used via settings (and/or
		// allow chaining of transformers in
		// icfgtransformer
		final ReplacementVarFactory fac = new ReplacementVarFactory(icfg.getCfgSmtToolkit(), false);

		final IPreferenceProvider ups = IcfgTransformationPreferences.getPreferenceProvider(mServices);
		final TransformationTestType transformation =
				ups.getEnum(IcfgTransformationPreferences.LABEL_TRANSFORMATION_TYPE, TransformationTestType.class);

		switch (transformation) {
		case LOOP_ACCELERATION_EXAMPLE:
			return applyLoopAccelerationEx(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_BIESENBACH:
			return applyLoopAccelerationBiesenbach(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case LOOP_ACCELERATION_MOHR:
			throw new UnsupportedOperationException("Mohr is missing implemented interface");
		case LOOP_ACCELERATION_WOELFING:
			return applyLoopAccelerationWoelfing(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case MAP_ELIMINATION:
			return applyMapElimination(icfg, locFac, outlocClass, backtranslationTracker, fac);
		case REMOVE_DIV_MOD:
			return applyRemoveDivMod(icfg, locFac, outlocClass, backtranslationTracker, fac);
		default:
			throw new UnsupportedOperationException("Unknown transformation type: " + transformation);
		}
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationWoelfing(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IBacktranslationTracker backtranslationTracker, final ReplacementVarFactory fac) {
		final ITransformulaTransformer transformer = new ExampleLoopAccelerationTransformulaTransformer(mLogger,
				icfg.getCfgSmtToolkit().getManagedScript(), icfg.getCfgSmtToolkit().getSymbolTable(), fac);
		return new LoopAccelerationIcfgTransformer<>(mLogger, icfg, locFac, backtranslationTracker, outlocClass,
				"IcfgWithLoopAccelerationWoelfing", transformer).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationBiesenbach(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IBacktranslationTracker backtranslationTracker, final ReplacementVarFactory fac) {
		final ITransformulaTransformer transformer = new ExampleLoopAccelerationTransformulaTransformer(mLogger,
				icfg.getCfgSmtToolkit().getManagedScript(), icfg.getCfgSmtToolkit().getSymbolTable(), fac);
		return new LoopDetectionBB<>(mLogger, icfg, outlocClass, locFac, "IcfgDuplicate", transformer,
				backtranslationTracker).getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyLoopAccelerationEx(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IBacktranslationTracker backtranslationTracker, final ReplacementVarFactory fac) {
		final ITransformulaTransformer transformer = new ExampleLoopAccelerationTransformulaTransformer(mLogger,
				icfg.getCfgSmtToolkit().getManagedScript(), icfg.getCfgSmtToolkit().getSymbolTable(), fac);
		return new IcfgTransformer<>(icfg, locFac, backtranslationTracker, outlocClass, "IcfgDuplicate", transformer)
				.getResult();
	}

	private static <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyRemoveDivMod(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IBacktranslationTracker backtranslationTracker, final ReplacementVarFactory fac) {
		IIcfg<OUTLOC> result;
		final ITransformulaTransformer transformer =
				new LocalTransformer(new RewriteDivision(fac), icfg.getCfgSmtToolkit().getManagedScript(), fac);
		final IcfgTransformer<INLOC, OUTLOC> icfgTransformer = new IcfgTransformer<>(icfg, locFac,
				backtranslationTracker, outlocClass, "TransformedIcfg", transformer);
		result = icfgTransformer.getResult();
		return result;
	}

	@SuppressWarnings("unchecked")
	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IIcfg<OUTLOC> applyMapElimination(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IBacktranslationTracker backtranslationTracker, final ReplacementVarFactory fac) {

		final List<ITransformulaTransformer> transformers = new ArrayList<>();
		transformers.add(new LocalTransformer(
				new DNF(mServices, icfg.getCfgSmtToolkit().getManagedScript(), mXnfConversionTechnique),
				icfg.getCfgSmtToolkit().getManagedScript(), fac));
		final IEqualityAnalysisResultProvider<IcfgLocation> equalityProvider = new DefaultEqualityAnalysisProvider<>();
		final MapEliminationSettings settings =
				new MapEliminationSettings(false, true, true, true, mSimplificationTechnique, mXnfConversionTechnique);
		transformers.add(new MapEliminationTransformer(mServices, mLogger, icfg.getCfgSmtToolkit().getManagedScript(),
				icfg.getCfgSmtToolkit().getSymbolTable(), fac, settings, equalityProvider));
		return new IcfgTransformerSequence<>(icfg, locFac, (ILocationFactory<OUTLOC, OUTLOC>) locFac,
				backtranslationTracker, outlocClass, "IcfgWithMapElim", transformers).getResult();
	}

	private static ILocationFactory<BoogieIcfgLocation, BoogieIcfgLocation> createBoogieLocationFactory() {
		return (oldLocation, debugIdentifier, procedure) -> {
			final BoogieIcfgLocation rtr = new BoogieIcfgLocation(debugIdentifier, procedure,
					oldLocation.isErrorLocation(), oldLocation.getBoogieASTNode());
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};
	}

	private static <INLOC extends IcfgLocation> ILocationFactory<INLOC, IcfgLocation> createIcfgLocationFactory() {
		return (oldLocation, debugIdentifier, procedure) -> {
			final IcfgLocation rtr = new IcfgLocation(debugIdentifier, procedure);
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};
	}

}
