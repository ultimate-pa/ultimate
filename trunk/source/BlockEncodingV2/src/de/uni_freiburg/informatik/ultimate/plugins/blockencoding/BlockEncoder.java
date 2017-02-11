/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.AssumeMerger;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.IEncoder;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.IcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.InterproceduralSequenzer;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.MaximizeFinalStates;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.MinimizeStatesMultiEdgeMultiNode;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.MinimizeStatesMultiEdgeSingleNode;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.MinimizeStatesSingleEdgeSingleNode;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.ParallelComposer;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.RemoveInfeasibleEdges;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.RemoveSinkStates;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding.Simplifier;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.PreferenceInitializer.MinimizeStates;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgSizeBenchmark;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BlockEncoder {

	private static final BuchiProgramAcceptingStateAnnotation BUCHI_PROGRAM_ACCEPTING_STATE_ANNOTATION =
			new BuchiProgramAcceptingStateAnnotation();

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final BlockEncodingBacktranslator mBacktranslator;
	private final IcfgEdgeBuilder mEdgeBuilder;

	private BasicIcfg<IcfgLocation> mIterationResult;

	public BlockEncoder(final ILogger logger, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final IcfgEdgeBuilder builder,
			final BasicIcfg<IcfgLocation> icfg) {
		mLogger = logger;
		mServices = services;
		mIterationResult = null;
		mBacktranslator = backtranslator;
		mEdgeBuilder = builder;
		processIcfg(icfg);
	}

	public IIcfg<?> getResult() {
		return mIterationResult;
	}

	private void processIcfg(final BasicIcfg<IcfgLocation> node) {
		// measure size of rcfg
		reportSizeBenchmark("Initial Icfg", node);

		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		int maxIters = ups.getInt(PreferenceInitializer.FXP_MAX_ITERATIONS) - 1;
		if (maxIters < 0) {
			maxIters = -1;
		}

		mIterationResult = node;
		final List<Supplier<IEncoder<IcfgLocation>>> encoderProviders = getEncoderProviders(ups, node);
		final boolean optimizeUntilFixpoint = ups.getBoolean(PreferenceInitializer.FXP_UNTIL_FIXPOINT);
		int i = 1;

		while (true) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("==== BE Pass #" + i + "====");
			}
			++i;
			EncodingResult currentResult = new EncodingResult(mIterationResult, false);

			for (final Supplier<IEncoder<IcfgLocation>> provider : encoderProviders) {
				final IEncoder<IcfgLocation> encoder = provider.get();
				currentResult = applyEncoder(currentResult, encoder);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Current error locations: " + IcfgUtils.getErrorLocations(currentResult.getIcfg()));
					new IcfgLocationIterator<>(currentResult.getIcfg()).asStream().forEach(a -> {
						mLogger.debug("Annotations of " + a);
						ModelUtils.consumeAnnotations(a, x -> mLogger.debug(x.getClass()));
					});
				}
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

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("==== BE Post Processing ====");
		}

		if (ups.getBoolean(PreferenceInitializer.POST_USE_PARALLEL_COMPOSITION)) {
			mIterationResult =
					new ParallelComposer(mEdgeBuilder, mServices, mBacktranslator).getResult(mIterationResult);
		}

		if (ups.getBoolean(PreferenceInitializer.POST_SIMPLIFY_CODEBLOCKS)) {
			mIterationResult = new Simplifier(mEdgeBuilder, mServices, mBacktranslator).getResult(mIterationResult);
		}

		reportSizeBenchmark("Encoded RCFG", mIterationResult);
	}

	private List<Supplier<IEncoder<IcfgLocation>>> getEncoderProviders(final IPreferenceProvider ups,
			final IIcfg<?> icfg) {
		final List<Supplier<IEncoder<IcfgLocation>>> rtr = new ArrayList<>();

		// note that the order is important

		if (ups.getBoolean(PreferenceInitializer.FXP_REMOVE_INFEASIBLE_EDGES)) {
			rtr.add(() -> new RemoveInfeasibleEdges(mServices, mBacktranslator));
		}

		if (ups.getBoolean(PreferenceInitializer.FXP_MAXIMIZE_FINAL_STATES)) {
			rtr.add(() -> new MaximizeFinalStates(mServices, BlockEncoder::markBuchiProgramAccepting,
					BlockEncoder::isBuchiProgramAccepting, mBacktranslator));
		}

		final MinimizeStates minimizeStates =
				ups.getEnum(PreferenceInitializer.FXP_MINIMIZE_STATES, MinimizeStates.class);
		if (minimizeStates != MinimizeStates.NONE) {
			switch (minimizeStates) {
			case SINGLE:

				rtr.add(() -> new MinimizeStatesSingleEdgeSingleNode(mEdgeBuilder, mServices, mBacktranslator,
						BlockEncoder::hasToBePreserved));
				break;
			case SINGLE_NODE_MULTI_EDGE:
				rtr.add(() -> new MinimizeStatesMultiEdgeSingleNode(mEdgeBuilder, mServices, mBacktranslator,
						BlockEncoder::hasToBePreserved));
				break;
			case MULTI:
				rtr.add(() -> new MinimizeStatesMultiEdgeMultiNode(mEdgeBuilder, mServices, mBacktranslator,
						BlockEncoder::hasToBePreserved));
				break;
			default:
				throw new IllegalArgumentException(minimizeStates + " is an unknown enum value!");
			}
		}

		if (ups.getBoolean(PreferenceInitializer.FXP_SIMPLIFY_ASSUMES)) {
			rtr.add(() -> new AssumeMerger(mEdgeBuilder, mServices, mBacktranslator));
		}

		if (ups.getBoolean(PreferenceInitializer.FXP_REMOVE_SINK_STATES)) {
			rtr.add(() -> new RemoveSinkStates(mServices, BlockEncoder::hasToBePreserved, mBacktranslator));
		}

		rtr.add(() -> new InterproceduralSequenzer(mEdgeBuilder, mServices, mBacktranslator));

		return rtr;
	}

	private static EncodingResult applyEncoder(final EncodingResult previousResult,
			final IEncoder<IcfgLocation> encoder) {
		final BasicIcfg<IcfgLocation> result = encoder.getResult(previousResult.getIcfg());
		return new EncodingResult(result, previousResult.isChanged() || encoder.isGraphStructureChanged());
	}

	private void reportSizeBenchmark(final String message, final IIcfg<?> root) {
		final IcfgSizeBenchmark bench = new IcfgSizeBenchmark(root, message);
		mLogger.info(message + " " + bench);
		bench.reportBenchmarkResult(mServices.getResultService(), Activator.PLUGIN_ID, message);
	}

	private static boolean hasToBePreserved(final IIcfg<?> icfg, final IcfgLocation node) {
		if (node == null) {
			return false;
		}
		if (node instanceof BoogieIcfgLocation) {
			final BoogieIcfgLocation pp = (BoogieIcfgLocation) node;
			return pp.isErrorLocation();
		}

		final String proc = node.getProcedure();
		final Set<?> errorNodes = icfg.getProcedureErrorNodes().get(proc);
		if (errorNodes != null && !errorNodes.isEmpty()) {
			return errorNodes.contains(node);
		}

		return false;
	}

	private static boolean isBuchiProgramAccepting(final IcfgLocation node) {
		return BuchiProgramAcceptingStateAnnotation.getAnnotation(node) != null;
	}

	private static void markBuchiProgramAccepting(final IcfgLocation node) {
		BUCHI_PROGRAM_ACCEPTING_STATE_ANNOTATION.annotate(node);
	}

	private static class EncodingResult {
		private final BasicIcfg<IcfgLocation> mNode;
		private final boolean mIsChanged;

		private EncodingResult(final BasicIcfg<IcfgLocation> node, final boolean isChanged) {
			mNode = node;
			mIsChanged = isChanged;
		}

		private boolean isChanged() {
			return mIsChanged;
		}

		private BasicIcfg<IcfgLocation> getIcfg() {
			return mNode;
		}
	}

}
