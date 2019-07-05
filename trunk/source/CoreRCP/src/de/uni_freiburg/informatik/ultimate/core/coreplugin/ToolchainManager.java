/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.CompleteToolchainData;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.GenericServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AssertionsEnabledResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.PluginType;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.SubchainType;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 *
 * The {@link ToolchainManager} controls the livecycle of all toolchains and the associated plugins.
 *
 * @author dietsch
 *
 */
public class ToolchainManager {

	private final ILogger mLogger;
	private final PluginFactory mPluginFactory;
	private final IController<RunDefinition> mCurrentController;
	private final AtomicLong mCurrentId;
	private final ConcurrentHashMap<Long, Toolchain> mActiveToolchains;
	private final ILoggingService mLoggingService;

	public ToolchainManager(final ILoggingService loggingService, final PluginFactory factory,
			final IController<RunDefinition> controller) {
		mLoggingService = loggingService;
		mLogger = mLoggingService.getLogger(Activator.PLUGIN_ID);
		mPluginFactory = factory;
		mCurrentController = controller;
		mCurrentId = new AtomicLong();
		mActiveToolchains = new ConcurrentHashMap<>();
	}

	public void releaseToolchain(final IToolchain<RunDefinition> toolchain) {
		if (toolchain == null) {
			throw new IllegalArgumentException("toolchain");
		}
		if (!mActiveToolchains.remove(toolchain.getId(), toolchain)) {
			mLogger.warn("An concurrency error occured: Toolchain ID has changed during livecycle");
		}
		if (toolchain.getCurrentToolchainData() != null && toolchain.getCurrentToolchainData().getStorage() != null) {
			toolchain.getCurrentToolchainData().getStorage().clear();
			mLogger.debug("Toolchain " + toolchain.getId() + " released");
		}
	}

	public IToolchain<RunDefinition> requestToolchain(final File[] inputFiles) {
		final Toolchain tc = new Toolchain(mCurrentId.incrementAndGet(), inputFiles, createModelManager());
		mActiveToolchains.put(tc.getId(), tc);
		return tc;
	}

	public void close() {
		// we should drop everything

		if (mActiveToolchains.size() > 0) {
			mLogger.info("There are still " + mActiveToolchains.size() + " active toolchains alive");
			final List<Toolchain> openChains = new ArrayList<>(mActiveToolchains.values());
			for (final Toolchain tc : openChains) {
				if (tc != null && tc.getCurrentToolchainData() != null
						&& tc.getCurrentToolchainData().getStorage() != null) {
					tc.getCurrentToolchainData().getStorage().clear();
				}
			}
			mActiveToolchains.clear();
		}
	}

	private IModelManager createModelManager() {
		return new PersistenceAwareModelManager(
				new RcpPreferenceProvider(Activator.PLUGIN_ID).getString(CorePreferenceInitializer.LABEL_TMP_DIRECTORY),
				mLogger);
	}

	/*************************** ToolchainContainer Implementation ****************************/
	private final class Toolchain implements IToolchain<RunDefinition> {

		private final long mId;
		private final IModelManager mModelManager;
		private final Benchmark mBenchmark;

		private IToolchainData<RunDefinition> mToolchainData;
		private final Map<File[], ISource> mFiles2Parser;
		private final File[] mInputFiles;
		private ToolchainWalker mToolchainWalker;

		Toolchain(final long id, final File[] inputFiles, final IModelManager modelManager) {
			mId = id;
			mModelManager = modelManager;
			mBenchmark = new Benchmark();
			mFiles2Parser = new LinkedHashMap<>();
			mInputFiles = Objects.requireNonNull(inputFiles);
		}

		/*************************** IToolchain<RunDefinition> Implementation ****************************/

		@Override
		public void init(final IToolchainProgressMonitor monitor) {
			if (mToolchainData == null) {
				return;
			}
			mToolchainWalker = new ToolchainWalker(mBenchmark, mModelManager, mPluginFactory, mLogger);

			mToolchainData.getStorage().clear();

			// install logging services into toolchain storage
			mLoggingService.setCurrentControllerID(mCurrentController.getPluginID());
			mLoggingService.store(mToolchainData.getStorage());

			// install service provider service into toolchain storage
			mToolchainData.getStorage().putStorable(GenericServiceProvider.getServiceKey(),
					new GenericServiceProvider(mPluginFactory));

			// install new ProgressMonitorService
			final ProgressMonitorService monitorService =
					new ProgressMonitorService(monitor, mLogger, mToolchainWalker);
			mToolchainData.getStorage().putStorable(ProgressMonitorService.getServiceKey(), monitorService);

		}

		@Override
		public IToolchainData<RunDefinition> makeToolSelection(final IToolchainProgressMonitor monitor) {
			final List<ITool> tools = mPluginFactory.getAllAvailableTools();

			if (tools.isEmpty()) {
				mLogger.warn(getLogPrefix() + ": There are no plugins present, returning null tools.");
				return null;
			}

			// present selection dialog
			final IToolchainData<RunDefinition> rtr = mCurrentController.selectTools(tools);
			return setToolSelection(monitor, rtr);
		}

		@Override
		public IToolchainData<RunDefinition> setToolSelection(final IToolchainProgressMonitor monitor,
				final IToolchainData<RunDefinition> data) {
			if (data == null) {
				/* dialog was aborted */
				mLogger.warn(getLogPrefix() + ": No toolchain found.");
				return null;
			}
			if (!checkToolchain(data.getRootElement().getToolchain().getPluginOrSubchain())) {
				mLogger.warn(getLogPrefix() + ": Invalid toolchain found.");
				return null;
			}
			mToolchainData = data;
			init(monitor);
			mLogger.info(getLogPrefix() + ": Toolchain selected.");
			return data;
		}

		@Override
		public boolean initializeParsers() {
			if (mInputFiles == null || mInputFiles.length == 0) {
				mLogger.fatal(getLogPrefix() + ": No input files specified");
				return false;
			}

			// compute which parser can parse which files
			final Set<ISource> parsers = loadParsers();
			final Set<File> alreadyParsable = new HashSet<>();
			for (final ISource parser : parsers) {
				final File[] parseableFiles = parser.parseable(mInputFiles);
				assert parseableFiles != null;
				if (parseableFiles.length > 0) {
					mFiles2Parser.put(parseableFiles, parser);
					for (final File parseableFile : parseableFiles) {
						if (!alreadyParsable.add(parseableFile)) {
							mLogger.warn("Multiple parsers will parse " + parseableFile.getAbsolutePath());
						}
					}
				}
			}

			// abort if we have no parsers
			if (mFiles2Parser.isEmpty()) {
				mLogger.warn(getLogPrefix() + ": No parsers available for " + getStringFromFiles(mInputFiles));
				return false;
			}

			final Set<File> allFiles = Arrays.stream(mInputFiles).collect(Collectors.toSet());
			final Set<File> selectedFiles = mFiles2Parser.entrySet().stream().flatMap(a -> Arrays.stream(a.getKey()))
					.collect(Collectors.toSet());
			if (!selectedFiles.containsAll(allFiles)) {
				// some files cannot be parsed
				final Set<File> notParseable = new HashSet<>(allFiles);
				notParseable.removeAll(selectedFiles);
				mLogger.warn(getLogPrefix() + ": No parsers available for " + getStringFromFiles(notParseable));
				return false;
			}

			mLogger.info(getLogPrefix() + ": Applicable parser(s) successfully (re)initialized");
			return true;
		}

		private String getStringFromFiles(final File[] files) {
			return getStringFromFiles(Arrays.stream(files));
		}

		private String getStringFromFiles(final Collection<File> files) {
			return getStringFromFiles(files.stream());
		}

		private String getStringFromFiles(final Stream<File> fileStream) {
			return fileStream.map(File::getAbsolutePath).collect(Collectors.joining(","));
		}

		@Override
		public void runParsers() throws Exception {
			for (final Entry<File[], ISource> entry : mFiles2Parser.entrySet()) {
				final ISource parser = entry.getValue();
				final File[] input = entry.getKey();

				// note that runParser has to happen before parser.getOutputDefinition() !
				@SuppressWarnings("squid:S1941")
				final IElement element = runParser(input, parser);
				final ModelType t = parser.getOutputDefinition();
				if (t == null) {
					final String errorMsg = parser.getPluginName() + " returned invalid output definition for file(s) "
							+ getStringFromFiles(input);
					mLogger.fatal(getLogPrefix() + ": " + errorMsg + ", aborting...");
					throw new IllegalArgumentException(errorMsg);
				}
				addAST(element, t);
			}
		}

		@Override
		public ReturnCode processToolchain(final IToolchainProgressMonitor monitor) throws Throwable {
			mLogger.info("####################### " + getLogPrefix() + " #######################");
			final RcpPreferenceProvider ups = new RcpPreferenceProvider(Activator.PLUGIN_ID);
			final boolean useBenchmark = ups.getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK);
			final IUltimateServiceProvider currentToolchainServices = mToolchainData.getServices();
			Benchmark bench = null;
			if (useBenchmark) {
				bench = new Benchmark();
				bench.start("Toolchain (without parser)");
			}
			try {
				if (mModelManager.size() < 1) {
					mLogger.error(getLogPrefix()
							+ ": There is no model present. Did you run a ISource or IGenerator plugin in your toolchain?");
					throw new IllegalStateException("There is no model present.");
				}

				final Collection<ISource> parsers = mFiles2Parser.values();
				final CompleteToolchainData data = new CompleteToolchainData(mToolchainData,
						parsers.toArray(new ISource[parsers.size()]), mCurrentController);
				data.getController().prerun(mToolchainData);
				return mToolchainWalker.walk(data, currentToolchainServices.getProgressMonitorService(), monitor);

			} finally {
				final IResultService resultService = currentToolchainServices.getResultService();
				if (VMUtils.areAssertionsEnabled()) {
					resultService.reportResult(Activator.PLUGIN_ID, new AssertionsEnabledResult(Activator.PLUGIN_ID));
				}

				if (useBenchmark) {
					bench.stopAll();
					bench.printResult(mLogger);
					mBenchmark.printResult(mLogger);

					// report benchmark results
					resultService.reportResult(Activator.PLUGIN_ID,
							new StatisticsResult<>(Activator.PLUGIN_ID, "Toolchain Benchmarks", mBenchmark));

				}

				mLogger.info("#######################  End " + getLogPrefix() + " #######################");
				// TODO: Move all result logging to the different controllers
				final ILogger controllerLogger = currentToolchainServices.getLoggingService().getControllerLogger();

				final boolean appendCompleteLongDescription =
						CorePreferenceInitializer.getPreferenceProvider(currentToolchainServices)
								.getBoolean(CorePreferenceInitializer.LABEL_LONG_RESULT);
				final boolean printStatisticResults =
						CorePreferenceInitializer.getPreferenceProvider(currentToolchainServices)
								.getBoolean(CorePreferenceInitializer.LABEL_PRINT_STATISTICS_RESULTS);
				final Map<String, List<IResult>> results;
				if (printStatisticResults) {
					results = resultService.getResults();
				} else {
					results = ResultUtil.filterResultMap(resultService.getResults(),
							p -> !(p instanceof StatisticsResult<?>));
				}
				ResultUtil.logResults(controllerLogger, results, appendCompleteLongDescription);
				mCurrentController.displayToolchainResults(mToolchainData, resultService.getResults());
				mModelManager.removeAll();
				mToolchainWalker.endToolchain();
			}
		}

		@Override
		public void addAST(final IElement root, final ModelType outputDefinition) {
			if (mModelManager.addItem(root, outputDefinition)) {
				mLogger.debug(getLogPrefix() + ": Successfully added AST to model manager");
			} else {
				mLogger.error(getLogPrefix() + ": Could not add AST to model manager!");
			}
		}

		@Override
		public long getId() {
			return mId;
		}

		/*************************** End IToolchain<RunDefinition> Implementation ****************************/

		/**
		 * Checks whether all plugins in the toolchain are present.
		 *
		 * @param chain
		 *            Toolchain description to check.
		 * @return <code>true</code> if and only if every plugin in the chain exists.
		 */
		private boolean checkToolchain(final List<Object> chain) {
			return chain.stream().allMatch(this::checkToolchainElement);
		}

		private boolean checkToolchainElement(final Object elem) {
			if (elem instanceof PluginType) {
				final PluginType plugin = (PluginType) elem;
				if (mPluginFactory.isPluginAvailable(plugin.getId())) {
					return true;
				}
				mLogger.error(getLogPrefix() + ": Did not find plugin with id \"" + plugin.getId()
						+ "\". The following plugins are currently available:");
				printAvailableTools();
				return false;
			} else if (elem instanceof SubchainType) {
				return checkToolchain(((SubchainType) elem).getPluginOrSubchain());
			} else {
				throw new IllegalArgumentException("Found unknown type in toolchain: " + elem.getClass());
			}
		}

		private void printAvailableTools() {
			if (!mLogger.isInfoEnabled()) {
				return;
			}
			for (final ITool t : mPluginFactory.getAllAvailableTools()) {
				mLogger.info(getLogPrefix() + ": " + t.getPluginID());
			}
		}

		private IElement runParser(final File[] input, final ISource parser) throws Exception {
			final boolean useBenchmark = new RcpPreferenceProvider(Activator.PLUGIN_ID)
					.getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK);
			IElement root = null;

			PluginConnector.initializePlugin(mLogger, parser, mToolchainData.getServices(),
					mToolchainData.getStorage());

			// parse the files to Graph
			try {

				if (useBenchmark) {
					mBenchmark.start(parser.getPluginName());
				}

				if (input.length == 1) {
					mLogger.info(getLogPrefix() + ": Parsing single file: " + input[0].getAbsolutePath());
				} else {
					mLogger.info(getLogPrefix() + ": Parsing files: " + getStringFromFiles(input));
				}

				if (useBenchmark) {
					mBenchmark.stop(parser.getPluginName());
				}
				root = parser.parseAST(input);

			} catch (final Exception e) {
				mLogger.fatal(getLogPrefix() + ": Exception during parsing: ", e);
				resetModelManager();
				throw e;
			} finally {
				parser.finish();
			}
			return root;
		}

		private void resetModelManager() {
			if (!mModelManager.isEmpty()) {
				mLogger.info(getLogPrefix() + ": Clearing model...");
				try {
					mModelManager.persistAll(false);
				} catch (final StoreObjectException e) {
					final Throwable cause = e.getCause();
					mLogger.error(getLogPrefix() + ": Failed to persist models: "
							+ (cause == null ? e.getMessage() : cause.getMessage()));
				}
			}
		}

		private Set<ISource> loadParsers() {
			final List<String> parserIds = mPluginFactory.getPluginClassNames(ISource.class);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogPrefix() + ": We have " + parserIds.size() + " parsers present.");
			}

			final Set<ISource> rtr = new HashSet<>();
			for (final String parserId : parserIds) {
				final ISource parser = mPluginFactory.createTool(parserId);
				if (parser == null) {
					mLogger.warn(getLogPrefix() + ": Parser with ID " + parserId + " could not be created");
					continue;
				}
				rtr.add(parser);
			}

			return rtr;
		}

		@Override
		public IToolchainData<RunDefinition> getCurrentToolchainData() {
			return mToolchainData;
		}

		private String getLogPrefix() {
			return "[Toolchain " + mId + "]";
		}

		@Override
		public File[] getInputFiles() {
			return mInputFiles;
		}
	}
	/*************************** End ToolchainContainer Implementation ****************************/
}
