/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 *
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LassoShapedNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.BacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.IOutput;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgGraphProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessPrinter implements IOutput {

	private ILogger mLogger;
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;
	private RCFGCatcher mRCFGCatcher;
	private boolean mMatchingModel;

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.ALL;
	}

	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		if ("de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder".equals(graphType.getCreator())) {
			mMatchingModel = true;
		} else {
			mMatchingModel = false;
		}
	}

	@Override
	public List<IObserver> getObservers() {
		if (mMatchingModel) {
			// we should create this class somewere in cacsl s.t. we get the correct parameters -- perhaps translation
			// service
			mRCFGCatcher = new RCFGCatcher();
			return Collections.singletonList(mRCFGCatcher);
		}
		return Collections.emptyList();
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		mStorage = storage;
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() {
		// not needed
	}

	@Override
	public void finish() {
		try {
			if (!mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getBoolean(PreferenceInitializer.LABEL_WITNESS_GEN)) {
				mLogger.info("Witness generation is disabled");
				return;
			}

			// determine if there are true or false witnesses
			final List<IResult> results = mServices.getResultService().getResults().entrySet().stream()
					.flatMap(a -> a.getValue().stream()).collect(Collectors.toList());

			final WitnessManager cexVerifier = new WitnessManager(mLogger, mServices, mStorage);
			if (results.stream().anyMatch(a -> a instanceof CounterExampleResult<?, ?, ?>)) {
				mLogger.info("Generating witness for reachability counterexample");
				generateReachabilityCounterexampleWitness(cexVerifier, results);
			} else if (results.stream().anyMatch(a -> a instanceof LassoShapedNonTerminationArgument<?, ?>)) {
				mLogger.info("Generating witness for non-termination counterexample");
				generateNonTerminationWitness(cexVerifier, results);
			} else if (results.stream().anyMatch(a -> a instanceof AllSpecificationsHoldResult)) {
				mLogger.info("Generating witness for correct program");
				generateProofWitness(cexVerifier, results);
			} else {
				mLogger.info("No result that supports witness generation found");
			}

		} catch (IOException | InterruptedException e) {
			throw new RuntimeException(e);
		}
	}

	private void generateProofWitness(final WitnessManager cexVerifier, final List<IResult> results)
			throws IOException, InterruptedException {
		final AllSpecificationsHoldResult result =
				ResultUtil.filterResults(results, AllSpecificationsHoldResult.class).stream().findFirst().orElse(null);
		final IBacktranslationService backtrans = mServices.getBacktranslationService();
		final BoogieIcfgContainer root = mRCFGCatcher.getModel();
		final String filename = ILocation.getAnnotation(root).getFileName();
		final BacktranslatedCFG<?, IcfgEdge> origCfg =
				new BacktranslatedCFG<>(filename, IcfgGraphProvider.getVirtualRoot(root), IcfgEdge.class);
		final String witness = new CorrectnessWitnessGenerator<>(backtrans.translateCFG(origCfg), mLogger, mServices)
				.makeGraphMLString();
		cexVerifier.run(Collections.singleton(new Triple<>(result, filename, witness)));
	}

	private void generateReachabilityCounterexampleWitness(final WitnessManager cexVerifier,
			final List<IResult> results) throws IOException, InterruptedException {
		final Collection<Triple<IResult, String, String>> suppliers = new ArrayList<>();
		final Collection<CounterExampleResult> cexResults =
				ResultUtil.filterResults(mServices.getResultService().getResults(), CounterExampleResult.class);
		final IBacktranslationService backtrans = mServices.getBacktranslationService();
		final BoogieIcfgContainer root = mRCFGCatcher.getModel();
		final String filename = ILocation.getAnnotation(root).getFileName();

		for (final CounterExampleResult<?, ?, ?> cex : cexResults) {
			final IProgramExecution<?, ?> backtransPe = backtrans.translateProgramExecution(cex.getProgramExecution());
			final String witness = new ViolationWitnessGenerator<>(backtransPe, mLogger, mServices).makeGraphMLString();
			suppliers.add(new Triple<>(cex, filename, witness));
		}
		cexVerifier.run(suppliers);
	}

	private void generateNonTerminationWitness(final WitnessManager cexVerifier, final List<IResult> results)
			throws IOException, InterruptedException {
		final Collection<Triple<IResult, String, String>> suppliers = new ArrayList<>();
		final Collection<LassoShapedNonTerminationArgument> cexResults = ResultUtil
				.filterResults(mServices.getResultService().getResults(), LassoShapedNonTerminationArgument.class);
		final IBacktranslationService backtrans = mServices.getBacktranslationService();
		final BoogieIcfgContainer root = mRCFGCatcher.getModel();
		final String filename = ILocation.getAnnotation(root).getFileName();

		for (final LassoShapedNonTerminationArgument<?, ?> cex : cexResults) {
			final IProgramExecution<?, ?> stem = backtrans.translateProgramExecution(cex.getStemExecution());
			final IProgramExecution<?, ?> loop = backtrans.translateProgramExecution(cex.getLoopExecution());
			final String witness = new ViolationWitnessGenerator<>(stem, mLogger, mServices).makeGraphMLString();
			suppliers.add(new Triple<>(cex, filename, witness));
		}
		cexVerifier.run(suppliers);
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}
}
