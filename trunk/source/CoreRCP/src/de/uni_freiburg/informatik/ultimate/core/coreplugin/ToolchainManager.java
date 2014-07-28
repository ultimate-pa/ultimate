package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.preferences.InstanceScope;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.CompleteToolchainData;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.PluginType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.SubchainType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.LoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.services.ProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IModelManager;
import de.uni_freiburg.informatik.ultimate.model.PersistenceAwareModelManager;
import de.uni_freiburg.informatik.ultimate.model.repository.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.plugins.ResultNotifier;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;

/**
 * 
 * The {@link ToolchainManager} controls the livecycle of all toolchains and the
 * associated plugins.
 * 
 * @author dietsch
 * 
 */
public class ToolchainManager {

	/*
	 * Plan: - Define toolchain - Prepare toolchain storage - set storage and
	 * services for each participating plugin - init plugin - create toolchain
	 * walker for plugin - let toolchain run - ask controller what should happen
	 * to toolchain - dispose toolchain
	 * 
	 * Many core fields belong to this class: modelmanager
	 */

	private final Logger mLogger;
	private final PluginFactory mPluginFactory;
	private final IController mCurrentController;
	private final AtomicLong mCurrentId;
	private final ConcurrentHashMap<Long, ToolchainContainer> mActiveToolchains;
	private final LoggingService mLoggingService;

	public ToolchainManager(LoggingService loggingService, PluginFactory factory, IController controller) {
		mLoggingService = loggingService;
		mLogger = mLoggingService.getLogger(Activator.s_PLUGIN_ID);
		mPluginFactory = factory;
		mCurrentController = controller;
		mCurrentId = new AtomicLong();
		mActiveToolchains = new ConcurrentHashMap<>();
	}

	public void releaseToolchain(IToolchain toolchain) {
		if (!mActiveToolchains.remove(toolchain.getId(), toolchain)) {
			mLogger.fatal("An concurrency error occured: Toolchain ID has changed during livecycle");
		}
		if (toolchain != null && toolchain.getCurrentToolchainData() != null
				&& toolchain.getCurrentToolchainData().getStorage() != null) {
			toolchain.getCurrentToolchainData().getStorage().clear();
			mLogger.debug("Toolchain " + toolchain.getId() + " released");
		}
	}

	public IToolchain requestToolchain() {
		ToolchainContainer tc = new ToolchainContainer(mCurrentId.incrementAndGet(), createModelManager());
		mActiveToolchains.put(tc.getId(), tc);
		return tc;
	}

	public void close() {
		// TODO: Old code in the core
		// if (new UltimatePreferenceStore(Activator.s_PLUGIN_ID).getBoolean(
		// CorePreferenceInitializer.LABEL_MM_DROP_MODELS, true)) {
		// for (String s : mModelManager.getItemNames()) {
		// mModelManager.removeItem(s);
		// }
		// }

		// we should drop everything

		if (mActiveToolchains.size() > 0) {
			mLogger.info("There are still " + mActiveToolchains.size() + " active toolchains alive");
			mActiveToolchains.clear();
		}
	}

	private IModelManager createModelManager() {
		String tmp_dir = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getString(CorePreferenceInitializer.LABEL_MM_TMPDIRECTORY);
		return new PersistenceAwareModelManager(tmp_dir, mLogger);
	}

	/*************************** ToolchainContainer Implementation ****************************/
	private class ToolchainContainer implements IToolchain {

		private final long mId;
		private final IModelManager mModelManager;
		private final ToolchainWalker mToolchainWalker;
		private final Benchmark mBenchmark;

		private ToolchainData mToolchainData;
		private ISource mParser;
		private File mInputFiles;

		private ToolchainContainer(long id, IModelManager modelManager) {
			mId = id;
			mModelManager = modelManager;
			mBenchmark = new Benchmark();
			mToolchainWalker = new ToolchainWalker(mBenchmark, mModelManager, mPluginFactory, mLogger);
		}

		/*************************** IToolchain Implementation ****************************/

		@Override
		public void resetCore() {
			// TODO Auto-generated method stub
			// is not needed anymore
		}

		@Override
		public void setInputFile(File files) {
			mInputFiles = files;
		}

		public ToolchainData makeToolSelection() {
			List<ITool> tools = mPluginFactory.getAllAvailableTools();

			if (tools.isEmpty()) {
				mLogger.warn("There are no plugins present, returning null tools.");
				return null;
			}

			// present selection dialog
			ToolchainData rtr = mCurrentController.selectTools(tools);
			if (rtr == null) {
				/* dialog was aborted */
				mLogger.warn("Dialog was aborted, returning null tools.");
				return null;
			}
			if (!checkToolchain(rtr.getToolchain().getPluginOrSubchain())) {
				mLogger.warn("Invalid toolchain selection, returning null tools.");
				return null;
			}

			// inject logging services
			mLoggingService.setCurrentControllerID(mCurrentController.getPluginID());
			rtr.getStorage().putStorable(LoggingService.getServiceKey(), mLoggingService);

			mLogger.info("Toolchain data selected.");
			mToolchainData = rtr;
			return rtr;
		}

		@Override
		public boolean initializeParser(PreludeProvider preludefile) {
			mParser = selectParser(mInputFiles);

			if (mParser == null) {
				mLogger.warn("No parsers available");
				return false;
			}

			// set prelude file if present
			if (preludefile != null) {
				mParser.setPreludeFile(preludefile.getPreludeFile());
			} else {
				mParser.setPreludeFile(null);
			}

			if (mParser.getOutputDefinition() == null) {
				mLogger.fatal("ISource returned invalid Output Definition, aborting...");
				return false;
			}

			mLogger.info("Parser successfully initiated...");

			return true;
		}

		@Override
		public void runParser() throws Exception {
			addAST(runParser(mInputFiles, mParser), mParser.getOutputDefinition());
		}

		@Override
		public IStatus processToolchain(IProgressMonitor monitor) throws Throwable {
			mLogger.info("#######################  Toolchain " + getId() + " #######################");
			boolean useBenchmark = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
					.getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK);
			Benchmark bench = null;
			if (useBenchmark) {
				bench = new Benchmark();
				bench.start("Toolchain (without parser)");
			}
			try {
				if (mModelManager.size() < 1) {
					mLogger.error("There is no model present. Did you run a ISource or IGenerator plugin in your toolchain?");
					throw new IllegalStateException("There is no model present.");
				}
				CompleteToolchainData data = mToolchainWalker.new CompleteToolchainData(mToolchainData, mParser,
						mCurrentController);

				// install new ProgressMonitorService
				ProgressMonitorService monitorService = new ProgressMonitorService(monitor, Long.MAX_VALUE, mLogger,
						mToolchainWalker);
				mToolchainData.getStorage().putStorable(ProgressMonitorService.getServiceKey(), monitorService);

				mToolchainWalker.walk(data, monitor);
			} finally {
				if (useBenchmark) {
					bench.stopAll();

					bench.report();
					mBenchmark.report();
					mToolchainData
							.getServices()
							.getResultService()
							.reportResult(
									Activator.s_PLUGIN_ID,
									new BenchmarkResult<Double>(Activator.s_PLUGIN_ID, "Toolchain Benchmarks",
											mBenchmark));
				}
				new ResultNotifier(mCurrentController, mToolchainData.getServices()).processResults();
				mModelManager.removeAll();
				mLogger.info("#######################  End Toolchain " + getId() + " #######################");
			}

			return Status.OK_STATUS;
		}

		@Override
		public void addAST(IElement root, GraphType outputDefinition) {
			if (mModelManager.addItem(root, outputDefinition)) {
				mLogger.debug("Successfully added AST to model manager");
			} else {
				mLogger.error("Could not add AST to model manager!");
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
		 * @return <code>true</code> if and only if every plugin in the chain
		 *         exists.
		 */
		private boolean checkToolchain(List<Object> chain) {
			for (Object o : chain) {
				if (o instanceof PluginType) {
					PluginType plugin = (PluginType) o;
					if (!mPluginFactory.isPluginAvailable(plugin.getId())) {
						mLogger.error("Did not find plugin with id \"" + plugin.getId()
								+ "\". The following plugins are currently available:");
						if (mLogger.isInfoEnabled()) {
							for (ITool t : mPluginFactory.getAllAvailableTools()) {
								mLogger.info(t.getPluginID());
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
			boolean useBenchmark = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
					.getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK);
			IElement root = null;

			PluginConnector
					.initializePlugin(mLogger, parser, mToolchainData.getServices(), mToolchainData.getStorage());

			// parse the files to Graph
			try {
				mLogger.info(String.format("Parsing single file: %s", file.getAbsolutePath()));
				if (useBenchmark) {
					mBenchmark.start(parser.getPluginName());
				}
				root = parser.parseAST(file);
				if (useBenchmark) {
					mBenchmark.stop(parser.getPluginName());
				}

				/*
				 * for testing purposes only for(ISerialization ser :
				 * m_SerializationPlugins) { ser.serialize(root,
				 * "c:\\test.txt"); INode in = ser.deserialize("c:\\test.txt");
				 * if(in == in) System.out.println(in.toString()); }
				 */
			} catch (Exception e) {
				mLogger.fatal("Parsing gives Exception", e);
				resetModelManager();
			}
			return root;
		}

		private void resetModelManager() {
			if (!mModelManager.isEmpty()) {
				mLogger.info("Clearing model...");
				try {
					mModelManager.persistAll(false);
				} catch (StoreObjectException e) {
					mLogger.error("Failed to persist Models", e);
				}
			}
			return;
		}

		private final ISource selectParser(final File files) {
			// how many parsers does m_SourcePlugins provide?
			ArrayList<ISource> usableParsers = new ArrayList<ISource>();
			ISource parser = null;
			List<String> parserIds = mPluginFactory.getPluginClassNames(ISource.class);
			mLogger.debug("We have " + parserIds.size() + " parsers present.");

			// how many of these parsers can be used on our input file?
			for (String parserId : parserIds) {
				ISource p = mPluginFactory.createTool(parserId);
				if (p != null && p.parseable(files)) {
					mLogger.info("Parser " + p.getPluginName() + " is usable.");
					usableParsers.add(p);
				}
			}

			boolean showusableparser = InstanceScope.INSTANCE.getNode(Activator.s_PLUGIN_ID).getBoolean(
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
		public ToolchainData getCurrentToolchainData() {
			return mToolchainData;
		}
	}
	/*************************** End ToolchainContainer Implementation ****************************/
}
