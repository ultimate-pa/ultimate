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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.benchmark.SizeBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.AssumeMerger;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.IEncoder;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.MaximizeFinalStates;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.MinimizeStatesMultiEdgeMultiNode;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.MinimizeStatesMultiEdgeSingleNode;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.MinimizeStatesSingleEdgeSingleNode;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.RemoveInfeasibleEdges;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.RemoveSinkStates;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.PreferenceInitializer.MinimizeStates;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BlockEncodingObserver implements IUnmanagedObserver {
	
	private static final BuchiProgramAcceptingStateAnnotation BUCHI_PROGRAM_ACCEPTING_STATE_ANNOTATION =
			new BuchiProgramAcceptingStateAnnotation();
	
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final BlockEncodingBacktranslator mBacktranslator;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;
	private BoogieIcfgContainer mIterationResult;
	
	public BlockEncodingObserver(final ILogger logger, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final SimplificationTechnique simplTech,
			final XnfConversionTechnique xnfConvTech) {
		mLogger = logger;
		mServices = services;
		mIterationResult = null;
		mBacktranslator = backtranslator;
		mSimplificationTechnique = simplTech;
		mXnfConversionTechnique = xnfConvTech;
	}
	
	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// no initialisation needed
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
		return mIterationResult;
	}
	
	@Override
	public boolean process(final IElement root) throws Exception {
		if (root instanceof BoogieIcfgContainer) {
			processIcfg((BoogieIcfgContainer) root);
			return false;
		}
		return true;
	}
	
	private void processIcfg(final BoogieIcfgContainer node) {
		// measure size of rcfg
		reportSizeBenchmark("Initial Icfg", node);
		
		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		int maxIters = ups.getInt(PreferenceInitializer.OPTIMIZE_MAX_ITERATIONS) - 1;
		if (maxIters < 0) {
			maxIters = -1;
		}
		
		final List<IEncoderProvider> encoderProviders = getEncoderProviders(ups);
		final boolean optimizeUntilFixpoint = ups.getBoolean(PreferenceInitializer.OPTIMIZE_UNTIL_FIXPOINT);
		int i = 1;
		mIterationResult = node;
		while (true) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("==== BE Pass #" + i + "====");
			}
			++i;
			EncodingResult currentResult = new EncodingResult(mIterationResult, false);
			
			for (final IEncoderProvider provider : encoderProviders) {
				final IEncoder encoder = provider.createEncoder(currentResult.getIcfg());
				currentResult = applyEncoder(currentResult, encoder);
			}
			
			mIterationResult = currentResult.getIcfg();
			
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				mServices.getResultService().reportResult(Activator.PLUGIN_ID,
						new TimeoutResult(Activator.PLUGIN_ID, "Timeout during block encoding"));
				return;
			}
			
			if (!optimizeUntilFixpoint || !currentResult.isChanged() || maxIters == 0) {
				break;
			}
			if (maxIters > 0) {
				maxIters--;
			}
		}
		reportSizeBenchmark("Encoded RCFG", mIterationResult);
	}
	
	private List<IEncoderProvider> getEncoderProviders(final IPreferenceProvider ups) {
		final List<IEncoderProvider> rtr = new ArrayList<>();
		
		// note that the order is important
		
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_REMOVE_INFEASIBLE_EDGES)) {
			rtr.add((node) -> new RemoveInfeasibleEdges(node, mServices));
		}
		
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_REMOVE_SINK_STATES)) {
			rtr.add((node) -> new RemoveSinkStates(node, mServices, BlockEncodingObserver::hasToBePreserved));
		}
		
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_MAXIMIZE_FINAL_STATES)) {
			rtr.add((node) -> new MaximizeFinalStates(node, mServices, BlockEncodingObserver::markBuchiProgramAccepting,
					BlockEncodingObserver::isBuchiProgramAccepting));
		}
		
		final MinimizeStates minimizeStates =
				ups.getEnum(PreferenceInitializer.OPTIMIZE_MINIMIZE_STATES, MinimizeStates.class);
		if (minimizeStates != MinimizeStates.NONE) {
			switch (minimizeStates) {
			case SINGLE:
				rtr.add((node) -> new MinimizeStatesSingleEdgeSingleNode(node, mServices, mSimplificationTechnique,
						mXnfConversionTechnique, mBacktranslator, BlockEncodingObserver::hasToBePreserved));
				break;
			case SINGLE_NODE_MULTI_EDGE:
				rtr.add((node) -> new MinimizeStatesMultiEdgeSingleNode(node, mServices, mSimplificationTechnique,
						mXnfConversionTechnique, mBacktranslator, BlockEncodingObserver::hasToBePreserved));
				break;
			case MULTI:
				rtr.add((node) -> new MinimizeStatesMultiEdgeMultiNode(node, mServices, mSimplificationTechnique,
						mXnfConversionTechnique, mBacktranslator, BlockEncodingObserver::hasToBePreserved));
				break;
			default:
				throw new IllegalArgumentException(minimizeStates + " is an unknown enum value!");
			}
		}
		
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_SIMPLIFY_ASSUMES)) {
			rtr.add((node) -> new AssumeMerger(node, mServices, mSimplificationTechnique, mXnfConversionTechnique,
					mBacktranslator));
		}
		return rtr;
	}
	
	private static EncodingResult applyEncoder(final EncodingResult previousResult, final IEncoder encoder) {
		final BoogieIcfgContainer result = encoder.getResult(previousResult.getIcfg());
		return new EncodingResult(result, previousResult.isChanged() || encoder.isGraphChanged());
	}
	
	private void reportSizeBenchmark(final String message, final BoogieIcfgContainer root) {
		reportSizeBenchmark(message, new SizeBenchmark(root, message));
	}
	
	private void reportSizeBenchmark(final String message, final SizeBenchmark bench) {
		mLogger.info(message + " " + bench);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new BenchmarkResult<>(Activator.PLUGIN_ID, message, bench));
	}
	
	private static boolean hasToBePreserved(final IcfgLocation node) {
		if (node instanceof BoogieIcfgLocation) {
			final BoogieIcfgLocation pp = (BoogieIcfgLocation) node;
			return pp.isErrorLocation();
		}
		return false;
	}
	
	private static boolean isBuchiProgramAccepting(final IcfgLocation node) {
		return BuchiProgramAcceptingStateAnnotation.getAnnotation(node) != null;
	}
	
	private static void markBuchiProgramAccepting(final IcfgLocation node) {
		BUCHI_PROGRAM_ACCEPTING_STATE_ANNOTATION.annotate(node);
	}
	
	@FunctionalInterface
	private static interface IEncoderProvider {
		IEncoder createEncoder(final BoogieIcfgContainer boogieIcfgContainer);
	}
	
	private static class EncodingResult {
		private final BoogieIcfgContainer mNode;
		private final boolean mIsChanged;
		
		private EncodingResult(final BoogieIcfgContainer node, final boolean isChanged) {
			mNode = node;
			mIsChanged = isChanged;
		}
		
		private boolean isChanged() {
			return mIsChanged;
		}
		
		private BoogieIcfgContainer getIcfg() {
			return mNode;
		}
	}
}
