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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.InstanceScope;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.CompleteToolchainData;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.toolchain.PluginType;
import de.uni_freiburg.informatik.ultimate.core.model.toolchain.SubchainType;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.GenericServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.services.LoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.ProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.model.IResultService;
import de.uni_freiburg.informatik.ultimate.model.repository.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.models.ModelType;
import de.uni_freiburg.informatik.ultimate.plugins.ResultNotifier;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.model.IResultWithSeverity.Severity;
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

	private final Logger mLogger;
	private final PluginFactory mPluginFactory;
	private final IController mCurrentController;
	private final AtomicLong mCurrentId;
	private final ConcurrentHashMap<Long, Toolchain> mActiveToolchains;
	private final LoggingService mLoggingService;

	public ToolchainManager(LoggingService loggingService, PluginFactory factory, IController controller) {
		mLoggingService = loggingService;
		mLogger = mLoggingService.getLogger(Activator.PLUGIN_ID);
		mPluginFactory = factory;
		mCurrentController = controller;
		mCurrentId = new AtomicLong();
		mActiveToolchains = new ConcurrentHashMap<>();
	}

	public void releaseToolchain(IToolchain toolchain) {
		if (!mActiveToolchains.remove(toolchain.getId(), toolchain)) {
			mLogger.warn("An concurrency error occured: Toolchain ID has changed during livecycle");
		}
		if (toolchain != null && toolchain.getCurrentToolchainData() != null
				&& toolchain.getCurrentToolchainData().getStorage() != null) {
			toolchain.getCurrentToolchainData().getStorage().clear();
			mLogger.debug("Toolchain " + toolchain.getId() + " released");
		}
	}

	public IToolchain requestToolchain() {
		Toolchain tc = new Toolchain(mCurrentId.incrementAndGet(), createModelManager());
		mActiveToolchains.put(tc.getId(), tc);
		return tc;
	}

	public void close() {
		// we should drop everything

		if (mActiveToolchains.size() > 0) {
			mLogger.info("There are still " + mActiveToolchains.size() + " active toolchains alive");
			List<Toolchain> openChains = new ArrayList<>(mActiveToolchains.values());
			for (Toolchain tc : openChains) {
				if (tc != null && tc.getCurrentToolchainData() != null
						&& tc.getCurrentToolchainData().getStorage() != null) {
					tc.getCurrentToolchainData().getStorage().clear();
				}
			}
			mActiveToolchains.clear();
		}
	}

	private IModelManager createModelManager() {
		String tmp_dir = new UltimatePreferenceStore(Activator.PLUGIN_ID)
				.getString(CorePreferenceInitializer.LABEL_MM_TMPDIRECTORY);
		return new PersistenceAwareModelManager(tmp_dir, mLogger);
	}

	/*************************** ToolchainContainer Implementation ****************************/
	private class Toolchain implements IToolchain {

		private final long mId;
		private final IModelManager mModelManager;
		private final Benchmark mBenchmark;

		private IToolchainData mToolchainData;
		private Map<File, ISource> mParsers;
		private File[] mInputFiles;
		private ToolchainWalker mToolchainWalker;

		private Toolchain(long id, IModelManager modelManager) {
			mId = id;
			mModelManager = modelManager;
			mBenchmark = new Benchmark();
			mParsers = new LinkedHashMap<File, ISource>();
		}

		/*************************** IToolchain Implementation ****************************/

		@Override
		public void init(IToolchainProgressMonitor monitor) {
			if (mToolchainData == null) {
				return;
			}
			mToolchainWalker = new ToolchainWalker(mBenchmark, mModelManager, mPluginFactory, mLogger);

			mToolchainData.getStorage().clear();

			// install logging services into toolchain storage
			mLoggingService.setCurrentControllerID(mCurrentController.getPluginID());
			mToolchainData.getStorage().putStorable(LoggingService.getServiceKey(), mLoggingService);

			// install service provider service into toolchain storage
			mToolchainData.getStorage().putStorable(GenericServiceProvider.getServiceKey(),
					new GenericServiceProvider(mPluginFactory));

			// install new ProgressMonitorService
			ProgressMonitorService monitorService = new ProgressMonitorService(monitor, mLogger, mToolchainWalker);
			mToolchainData.getStorage().putStorable(ProgressMonitorService.getServiceKey(), monitorService);

		}

		@Override
		public void setInputFiles(File[] files) {
			mInputFiles = files;
		}

		@Override
		public IToolchainData makeToolSelection(final IToolchainProgressMonitor monitor) {
			List<ITool> tools = mPluginFactory.getAllAvailableTools();

			if (tools.isEmpty()) {
				mLogger.warn(getLogPrefix() + ": There are no plugins present, returning null tools.");
				return null;
			}

			// present selection dialog
			IToolchainData rtr = mCurrentController.selectTools(tools);
			return setToolSelection(monitor, rtr);
		}

		@Override
		public IToolchainData setToolSelection(final IToolchainProgressMonitor monitor, final IToolchainData data) {
			if (data == null) {
				/* dialog was aborted */
				mLogger.warn(getLogPrefix() + ": Dialog was aborted, returning null tools.");
				return null;
			}
			if (!checkToolchain(data.getToolchain().getPluginOrSubchain())) {
				mLogger.warn(getLogPrefix() + ": Invalid toolchain selection, returning null tools.");
				return null;
			}
			mToolchainData = data;
			init(monitor);
			mLogger.info(getLogPrefix() + ": Toolchain data selected.");
			return data;
		}

		@Override
		public boolean initializeParsers() {
			if (mInputFiles == null || mInputFiles.length == 0) {
				mLogger.fatal(getLogPrefix() + ": No input files specified");
				return false;
			}

			for (File inputFile : mInputFiles) {
				ISource parser = selectParser(inputFile);

				if (parser == null) {
					mLogger.warn(getLogPrefix() + ": No parsers available for " + inputFile.getAbsolutePath());
					return false;
				}

				// TODO: remove preludes from parser interface
				parser.setPreludeFile(null);
				mParsers.put(inputFile, parser);
			}
			mLogger.info(getLogPrefix() + ": Parser(s) successfully initiated...");
			return true;
		}

		@Override
		public void runParsers() throws Exception {
			for (Entry<File, ISource> entry : mParsers.entrySet()) {
				ISource parser = entry.getValue();
				File input = entry.getKey();

				IElement element = runParser(input, parser);
				ModelType t = parser.getOutputDefinition();
				if (t == null) {
					String errorMsg = parser.getPluginName() + " returned invalid output definition for file "
							+ input.getAbsolutePath();
					mLogger.fatal(getLogPrefix() + ": " + errorMsg + ", aborting...");
					throw new IllegalArgumentException(errorMsg);
				}
				addAST(element, t);
			}
		}

		@Override
		public ReturnCode processToolchain(IToolchainProgressMonitor monitor) throws Throwable {
			mLogger.info("####################### " + getLogPrefix() + " #######################");
			UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
			boolean useBenchmark = ups.getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK);
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

				CompleteToolchainData data = mToolchainWalker.new CompleteToolchainData(mToolchainData,
						mParsers.values().toArray(new ISource[0]), mCurrentController);

				mToolchainWalker.walk(data, mToolchainData.getServices().getProgressMonitorService(), monitor);

			} finally {
				IResultService resultService = mToolchainData.getServices().getResultService();
				// resultService.reportResult(Activator.s_PLUGIN_ID, new
				// GenericResult(Activator.s_PLUGIN_ID,
				// "VM Information", VMUtils.getVMInfos(), Severity.INFO));
				if (VMUtils.areAssertionsEnabled()) {
					resultService.reportResult(Activator.PLUGIN_ID, new GenericResult(Activator.PLUGIN_ID,
							"Assertions are enabled", "Assertions are enabled", Severity.INFO));
				}

				if (useBenchmark) {
					bench.stopAll();
					bench.printResult();
					mBenchmark.printResult();

					// report benchmark results
					resultService.reportResult(Activator.PLUGIN_ID,
							new BenchmarkResult<Double>(Activator.PLUGIN_ID, "Toolchain Benchmarks", mBenchmark));

				}

				new ResultNotifier(mCurrentController, mToolchainData.getServices()).processResults();
				mModelManager.removeAll();
				mLogger.info("#######################  End " + getLogPrefix() + " #######################");
			}

			return ReturnCode.Ok;
		}

		@Override
		public void addAST(IElement root, ModelType outputDefinition) {
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

		@Override
		public boolean hasInputFiles() {
			return mInputFiles != null;
		}

		/*************************** End IToolchain Implementation ****************************/

		/**
		 * Checks whether all plugins in the toolchain are present.
		 * 
		 * @param chain
		 *            Toolchain description to check.
		 * @return <code>true</code> if and only if every plugin in the chain exists.
		 */
		private boolean checkToolchain(List<Object> chain) {
			for (Object o : chain) {
				if (o instanceof PluginType) {
					PluginType plugin = (PluginType) o;
					if (!mPluginFactory.isPluginAvailable(plugin.getId())) {
						mLogger.error(getLogPrefix() + ": Did not find plugin with id \"" + plugin.getId()
								+ "\". The following plugins are currently available:");
						if (mLogger.isInfoEnabled()) {
							for (ITool t : mPluginFactory.getAllAvailableTools()) {
								mLogger.info(getLogPrefix() + ": " + t.getPluginID());
							}
						}
						return false;
					}
				} else if (o instanceof SubchainType) {
					SubchainType sub = (SubchainType) o;
					if (!checkToolchain(sub.getPluginOrSubchain()))
						// Did already log...
						return false;
				}
			}
			return true;
		}

		private final IElement runParser(final File file, ISource parser) throws Exception {
			boolean useBenchmark = new UltimatePreferenceStore(Activator.PLUGIN_ID)
					.getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK);
			IElement root = null;

			PluginConnector.initializePlugin(mLogger, parser, mToolchainData.getServices(),
					mToolchainData.getStorage());

			// parse the files to Graph
			try {
				mLogger.info(String.format(getLogPrefix() + ": Parsing single file: %s", file.getAbsolutePath()));
				if (useBenchmark) {
					mBenchmark.start(parser.getPluginName());
				}
				root = parser.parseAST(file);
				if (useBenchmark) {
					mBenchmark.stop(parser.getPluginName());
				}

				/*
				 * for testing purposes only for(ISerialization ser : m_SerializationPlugins) { ser.serialize(root,
				 * "c:\\test.txt"); INode in = ser.deserialize("c:\\test.txt"); if(in == in)
				 * System.out.println(in.toString()); }
				 */
			} catch (Exception e) {
				mLogger.fatal(getLogPrefix() + ": Exception during parsing: " + e.getMessage());
				resetModelManager();
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
				} catch (StoreObjectException e) {
					final Throwable cause = e.getCause();
					mLogger.error(getLogPrefix() + ": Failed to persist models: "
							+ (cause == null ? e.getMessage() : cause.getMessage()));
				}
			}
			return;
		}

		private final ISource selectParser(final File file) {
			// how many parsers does m_SourcePlugins provide?
			ArrayList<ISource> usableParsers = new ArrayList<ISource>();
			ISource parser = null;
			List<String> parserIds = mPluginFactory.getPluginClassNames(ISource.class);
			mLogger.debug(getLogPrefix() + ": We have " + parserIds.size() + " parsers present.");

			// how many of these parsers can be used on our input file?
			for (String parserId : parserIds) {
				ISource p = mPluginFactory.createTool(parserId);
				if (p != null && p.parseable(file)) {
					mLogger.info(getLogPrefix() + ": Parser " + p.getPluginName() + " is usable for "
							+ file.getAbsolutePath());
					usableParsers.add(p);
				} else {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(getLogPrefix() + ": Parser " + p.getPluginName() + " is not usable for "
								+ file.getAbsolutePath());
					}
				}
			}

			boolean showusableparser = InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID).getBoolean(
					CorePreferenceInitializer.LABEL_SHOWUSABLEPARSER,
					CorePreferenceInitializer.VALUE_SHOWUSABLEPARSER_DEFAULT);

			// if only parser can be used, choose it!
			if (usableParsers.size() == 1 && !showusableparser) {
				parser = usableParsers.get(0);
			} else if (usableParsers.isEmpty()) {
				return null;
			} else {
				// otherwise use parser choosing mechanism provided by
				// Controller
				parser = mCurrentController.selectParser(usableParsers);
			}

			return parser;
		}

		@Override
		public IToolchainData getCurrentToolchainData() {
			return mToolchainData;
		}

		private String getLogPrefix() {
			return "[Toolchain " + mId + "]";
		}
	}
	/*************************** End ToolchainContainer Implementation ****************************/
}
