package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.osgi.service.prefs.BackingStoreException;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.PluginType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.SubchainType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IModelManager;
import de.uni_freiburg.informatik.ultimate.model.PersistenceAwareModelManager;
import de.uni_freiburg.informatik.ultimate.model.repository.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.plugins.ResultNotifier;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;

/**
 * This class controls all aspects of the application's execution. This class
 * needs complete refactoring, perhaps even rewrite from scratch - DD
 * 
 * @author Jakob, Dietsch, Bjoern Buchhold, Christian Simon
 */
public class UltimateCore implements IApplication, ICore, IUltimatePlugin {

	private boolean mGuiMode;

	private Logger mLogger;

	private ArrayList<IOutput> mOutputPlugins;

	private ArrayList<IGenerator> mGeneratorPlugins;

	private ArrayList<IAnalysis> mAnalysisPlugins;

	private IController mCurrentController;

	private ArrayList<ISource> mSourcePlugins;

	private ISource mCurrentParser;

	private File mCurrentFiles;

	private Toolchain mCurrentToolchain;

	private ArrayList<ITool> mTools;

	/**
	 * the same content as m_AllTools, but as a mapping of tool ids to the
	 * actual tools
	 */
	private HashMap<String, ITool> mIdToTool;

	private Benchmark mBenchmark;

	/**
	 * mModelManager is used to store all different models of the framework. It
	 * should also provide save and load functions and is responsible for memory
	 * management
	 */
	private IModelManager mModelManager;

	/**
	 * What arguments were passed to the Ultimate RCP product before start-up?
	 */
	private CommandLineParser mCmdLineArgs;

	private ToolchainWalker mToolchainWalker;

	private IProgressMonitor mCurrentToolchainMonitor;
	private long mDeadline;

	private HashMap<String, LogPreferenceChangeListener> mActivePreferenceListener;

	/**
	 * This Default-Constructor is needed to start up the application
	 */
	public UltimateCore() {

	}

	public final Object start(IController controller, boolean isGraphical) throws Exception {
		mCurrentController = controller;
		mGuiMode = isGraphical;
		return start(null);
	}

	/**
	 * Method which is called by Eclipse framework. Compare to "main"-method.
	 * 
	 * @param context
	 *            Eclipse application context.
	 * @return Should return IPlatformRunnable.EXIT_OK or s.th. similar.
	 * @see org.eclipse.core.runtime.IPlatformRunnable#run(java.lang.Object)
	 * @throws Exception
	 *             May throw any exception
	 */
	@Override
	public final Object start(IApplicationContext context) throws Exception {

		// parse command line parameters and select ultimate mode
		mCmdLineArgs = new CommandLineParser();
		mCmdLineArgs.parse(Platform.getCommandLineArgs());

		// determine Ultimate's mode
		if (mCmdLineArgs.getExitSwitch()) {
			mCmdLineArgs.printUsage();
			return IApplication.EXIT_OK;
		}

		// initializing variables, loggers,...
		init();

		// loading classes exported by plugins
		loadExtension();

		// initialize the tools map
		initiateToolMaps();

		String settingsfile = mCmdLineArgs.getSettings();
		if (settingsfile != null) {
			loadPreferencesInternal(settingsfile);
		}

		// at this point a controller is already selected. We delegate control
		// to this controller.
		Object rtrCode = initializeController();

		// Ultimate is closing; should we clear the model store?
		if (new UltimatePreferenceStore(Activator.s_PLUGIN_ID).getBoolean(
				CorePreferenceInitializer.LABEL_MM_DROP_MODELS, true)) {
			for (String s : mModelManager.getItemNames()) {
				mModelManager.removeItem(s);
			}
		}
		cleanup();
		return rtrCode;
	}

	private int initializeController() {
		mLogger.info("Initializing controller ...");
		if (mCurrentController == null) {
			mLogger.fatal("No controller present! Ultimate will exit.");
			throw new NullPointerException("No controller present!");
		}
		int returnCode = mCurrentController.init(this);
		mLogger.info("Preparing to exit Ultimate with return code " + returnCode);
		return returnCode;
	}

	/**
	 * Initialization of private variables. Configures the Logging Subsystem and
	 * adds the first appender. this function must be called before the first
	 * usage of the logging subsystem
	 * 
	 */
	private void init() {
		UltimateServices.createInstance(this);

		mLogger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

		mLogger.info("Initializing application");

		// get tmp directory, use JAVA tmp dir by default
		String tmp_dir = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getString(CorePreferenceInitializer.LABEL_MM_TMPDIRECTORY);

		mActivePreferenceListener = new HashMap<String, LogPreferenceChangeListener>();
		mModelManager = new PersistenceAwareModelManager(tmp_dir);
		mOutputPlugins = new ArrayList<IOutput>();
		mSourcePlugins = new ArrayList<ISource>();
		mGeneratorPlugins = new ArrayList<IGenerator>();
		mAnalysisPlugins = new ArrayList<IAnalysis>();

		if (mDeadline == 0) {
			mDeadline = Long.MAX_VALUE;
		}
		mIdToTool = new HashMap<String, ITool>();
		mCurrentParser = null;
		mCurrentFiles = null;
		if (new UltimatePreferenceStore(Activator.s_PLUGIN_ID).getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK)) {
			mBenchmark = new Benchmark();
		} else {
			mBenchmark = null;
		}

		// initialize walker with common variables
		mToolchainWalker = new ToolchainWalker(this, mBenchmark, mModelManager, mIdToTool);

		UltimateServices.getInstance().setModelManager(mModelManager);
		final Logger tmp = mLogger;
		Job.getJobManager().addJobChangeListener(new JobChangeAdapter() {

			@Override
			public void done(IJobChangeEvent event) {
				if (event.getResult().getException() != null) {
					tmp.error("Error during toolchain job processing:", event.getResult().getException());
					if (Platform.inDebugMode() || Platform.inDevelopmentMode())
						event.getResult().getException().printStackTrace();
				}
			}

		});
		mLogger.info("--------------------------------------------------------------------------------");

	}

	/**
	 * Attaches Listener to all preferences and all scopes of all plugins to
	 * notify developers about changing preferences and prints loaded default
	 * values for all plugins
	 */
	private void checkPreferencesForActivePlugins() {

		attachLogPreferenceChangeListenerToPlugin(Activator.s_PLUGIN_ID);
		logDefaultPreferences(Activator.s_PLUGIN_ID);

		if (mCurrentController == null) {
			mLogger.warn("There is no Controller plugin");
		} else {
			attachLogPreferenceChangeListenerToPlugin(mCurrentController.getPluginID());
			logDefaultPreferences(mCurrentController.getPluginID());
		}

		for (IUltimatePlugin t : mOutputPlugins) {
			attachLogPreferenceChangeListenerToPlugin(t.getPluginID());
			logDefaultPreferences(t.getPluginID());
		}
		for (IUltimatePlugin t : mSourcePlugins) {
			attachLogPreferenceChangeListenerToPlugin(t.getPluginID());
			logDefaultPreferences(t.getPluginID());
		}
		for (IUltimatePlugin t : mGeneratorPlugins) {
			attachLogPreferenceChangeListenerToPlugin(t.getPluginID());
			logDefaultPreferences(t.getPluginID());
		}

		for (IUltimatePlugin t : mAnalysisPlugins) {
			attachLogPreferenceChangeListenerToPlugin(t.getPluginID());
			logDefaultPreferences(t.getPluginID());
		}

	}

	private void logDefaultPreferences(String pluginID) {
		UltimatePreferenceStore ups = new UltimatePreferenceStore(pluginID);
		try {
			IEclipsePreferences defaults = ups.getDefaultEclipsePreferences();
			String prefix = "[" + pluginID + " (Current)] Preference \"";
			for (String key : defaults.keys()) {
				mLogger.debug(prefix + key + "\" = " + ups.getString(key, "NOT DEFINED"));
			}
		} catch (BackingStoreException e) {
			mLogger.debug("An exception occurred during printing of default preferences for plugin " + pluginID + ":"
					+ e.getMessage());
		}
	}

	/**
	 * Attaches Listener to all preferences and all scopes of all plugins to
	 * notify developers about changing preferences
	 * 
	 * @param pluginId
	 */
	private void attachLogPreferenceChangeListenerToPlugin(String pluginId) {

		LogPreferenceChangeListener instanceListener = retrieveListener(pluginId, "Instance");
		LogPreferenceChangeListener configListener = retrieveListener(pluginId, "Configuration");
		LogPreferenceChangeListener defaultListener = retrieveListener(pluginId, "Default");

		InstanceScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(instanceListener);
		InstanceScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(instanceListener);

		ConfigurationScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(configListener);
		ConfigurationScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(configListener);

		DefaultScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(defaultListener);
		DefaultScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(defaultListener);
	}

	private LogPreferenceChangeListener retrieveListener(String pluginID, String scope) {
		String listenerID = pluginID + scope;
		if (mActivePreferenceListener.containsKey(listenerID)) {
			return mActivePreferenceListener.get(listenerID);
		} else {
			LogPreferenceChangeListener listener = new LogPreferenceChangeListener(scope, pluginID);
			mActivePreferenceListener.put(listenerID, listener);
			return listener;
		}
	}

	/**
	 * Creates instances of plugin classes.
	 * 
	 * @throws CoreException
	 * 
	 */
	private void loadExtension() throws CoreException {
		IExtensionRegistry reg = Platform.getExtensionRegistry();
		mLogger.info("Loading Plugins...");
		loadControllerPlugins(reg);
		loadOutputPlugins(reg);
		loadSourcePlugins(reg);

		loadGeneratorPlugins(reg);
		loadAnalysisPlugins(reg);
		mLogger.debug("--------------------------------------------------------------------------------");
		mLogger.debug("Loaded default settings");
		checkPreferencesForActivePlugins();
		mLogger.debug("--------------------------------------------------------------------------------");
		mLogger.info("Finished loading Plugins !");
		mLogger.info("--------------------------------------------------------------------------------");
	}

	/**
	 * This method loads all contributions to the IController Extension Point.
	 * Its receiving configuration elements (see exsd-files) which define class
	 * name in element "impl" and attribute "class" as well as an attribute
	 * "isGraphical". It then
	 * 
	 * Changed in Ultimate 2.0 to support multiple present controllers and to
	 * make the distinction between graphical and non graphical ones
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 * @throws CoreException
	 */
	private void loadControllerPlugins(IExtensionRegistry reg) throws CoreException {

		IConfigurationElement[] configElements = reg.getConfigurationElementsFor(ExtensionPoints.EP_CONTROLLER);

		if (configElements.length != 1) {
			mLogger.fatal("Invalid configuration. You should have only 1 IController plugin, but you have "
					+ configElements.length);
			if (configElements.length == 0) {
				return;
			}

			for (IConfigurationElement elem : configElements) {
				mLogger.fatal(((IController) elem.createExecutableExtension("class")).getClass());
			}

		}

		if (mCurrentController == null) {
			mGuiMode = new Boolean(configElements[0].getAttribute("isGraphical")).booleanValue();
			mCurrentController = (IController) (configElements[0].createExecutableExtension("class"));
		}
	}

	/**
	 * This method loads all contributions to the IOutput Extension Point. Its
	 * receiving configuration elements (see exsd-files) which define class name
	 * in element "impl" and attribute "class". If Ultimate is not running in
	 * GUI mode, all plug-ins requiring a GUI will be omitted.
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 */
	private void loadOutputPlugins(IExtensionRegistry reg) {
		IConfigurationElement[] configElements_out = reg.getConfigurationElementsFor(ExtensionPoints.EP_OUTPUT);
		mLogger.debug("We have " + configElements_out.length + " possible Output plugin(s)");
		for (IConfigurationElement element : configElements_out) {
			try {
				IOutput output = (IOutput) element.createExecutableExtension("class");
				// skip gui plug-ins if not running in GUI mode
				if (!(output.isGuiRequired() && !mGuiMode)) {
					mOutputPlugins.add(output);
				} else {
					mLogger.error("Can't load a gui plugin in command-line mode!");
				}
			} catch (CoreException e) {
				mLogger.error("Can't load a Output Plugin !", e);
			}
		}
		mLogger.info("Loaded " + mOutputPlugins.size() + " Output Plugins");
	}

	/**
	 * This method loads all contributions to the ISource Extension Point. Its
	 * receiving configuration elements (see exsd-files) which define class name
	 * in element "impl" and attribute "class".
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 */
	private void loadSourcePlugins(IExtensionRegistry reg) {
		IConfigurationElement[] configElements_source = reg.getConfigurationElementsFor(ExtensionPoints.EP_SOURCE);
		mLogger.debug("We have " + configElements_source.length + " possible Source plugin(s)");
		for (IConfigurationElement element : configElements_source) {
			try {
				ISource source = (ISource) element.createExecutableExtension("class");
				mSourcePlugins.add(source);
			} catch (CoreException e) {
				mLogger.error("Can't load a Source Plugin !", e);
			}
		}
		mLogger.info("Loaded " + mSourcePlugins.size() + " Source Plugins");

	}

	/**
	 * This method loads all contributions to the IGenerator Extension Point.
	 * Its receiving configuration elements (see exsd-files) which define class
	 * name in element "impl" and attribute "class".
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 */
	private void loadGeneratorPlugins(IExtensionRegistry reg) {
		IConfigurationElement[] configElements_gen = reg.getConfigurationElementsFor(ExtensionPoints.EP_GENERATOR);
		for (IConfigurationElement element : configElements_gen) {
			try {
				IGenerator generator = (IGenerator) element.createExecutableExtension("class");
				// skip gui plug-ins if not running in GUI mode
				if (!(generator.isGuiRequired() && !mGuiMode)) {
					mGeneratorPlugins.add(generator);
				} else {
					mLogger.error("Can't load a gui plugin in command-line mode!");
				}
			} catch (CoreException e) {
				mLogger.error("Can't load a Generator Plugin !", e);
			}
		}
		mLogger.info("Loaded " + mGeneratorPlugins.size() + " Generator Plugins");
	}

	/**
	 * This method loads all contributions to the Ianalysis Extension Point. Its
	 * receiving configuration elements (see exsd-files) which define class name
	 * in element "impl" and attribute "class".
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 */
	private void loadAnalysisPlugins(IExtensionRegistry reg) {
		IConfigurationElement[] configElements_out = reg.getConfigurationElementsFor(ExtensionPoints.EP_ANALYSIS);
		mLogger.debug("We have " + configElements_out.length + " possible analysis plugin(s)");
		for (IConfigurationElement element : configElements_out) {
			try {
				IAnalysis analysis = (IAnalysis) element.createExecutableExtension("class");
				// skip gui plug-ins if not running in GUI mode
				if (!(analysis.isGuiRequired() && !mGuiMode))
					mAnalysisPlugins.add(analysis);
				else
					mLogger.error("Can't load a gui plugin in command-line mode!");
			} catch (CoreException e) {
				mLogger.error("Can't load an analysis Plugin !", e);
			}
		}
		mLogger.info("Loaded " + mAnalysisPlugins.size() + " analysis Plugins");
	}

	/**
	 * This method calls init methods of bound plugins. This is useful for the
	 * first loading of plug-ins and for re-initializing plug-ins that have been
	 * used in a toolchain.
	 */
	private void initializePlugins() {
		mLogger.info("Initializing Plugins...");

		// re-initialize already opened plugins
		if (this.mToolchainWalker.getOpenPlugins().size() != 0) {
			for (String s : this.mToolchainWalker.getOpenPlugins().keySet()) {
				ITool t = mIdToTool.get(s);
				if (t != null) {
					t.init();
				}
			}
		} else {
			for (IOutput out : mOutputPlugins) {
				mLogger.info("Initializing " + out.getName() + "...");
				out.init();
			}
			for (IGenerator trans : mGeneratorPlugins) {
				mLogger.info("Initializing " + trans.getName() + "...");
				trans.init();
			}
			for (IAnalysis trans : mAnalysisPlugins) {
				mLogger.info("Initializing " + trans.getName() + "...");
				trans.init();
			}
		}
		for (ISource source : mSourcePlugins) {
			mLogger.info("Initializing " + source.getName() + "...");
			source.init();
		}

		mLogger.info("Finished initializing Plugins !");
		mLogger.info("--------------------------------------------------------------------------------");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore#resetCore()
	 */
	@Override
	public void resetCore() {
		initializePlugins();
		resetModelManager();
		if (new UltimatePreferenceStore(Activator.s_PLUGIN_ID).getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK)) {
			mBenchmark = new Benchmark();
		} else {
			mBenchmark = null;
		}
		// mToolchainWalker.reset();
		mToolchainWalker = new ToolchainWalker(this, mBenchmark, mModelManager, mIdToTool);
	}

	@Override
	public void setInputFile(File files) {
		mCurrentFiles = files;
	}

	@Override
	public boolean initiateParser(PreludeProvider preludefile) {
		mCurrentParser = selectParser(mCurrentFiles);

		if (mCurrentParser == null) {
			mLogger.warn("No parsers available");
			return false;
		}

		// set prelude file if present
		if (preludefile != null) {
			mCurrentParser.setPreludeFile(preludefile.getPreludeFile());
		} else {
			mCurrentParser.setPreludeFile(null);
		}

		if (mCurrentParser.getOutputDefinition() == null) {
			mLogger.fatal("ISource returned invalid Output Definition, aborting...");
			return false;
		}

		mLogger.info("Parser successfully initiated...");

		return true;
	}

	@Override
	public void runParser() throws Exception {
		addAST(runParser(mCurrentFiles, mCurrentParser), mCurrentParser.getOutputDefinition());
	}

	public void addAST(IElement root, GraphType outputDefinition) {
		if (mModelManager.addItem(root, outputDefinition)) {
			mLogger.debug("Successfully added AST to model manager");
		} else {
			mLogger.error("Could not add AST to model manager!");
		}
	}

	private void initiateToolMaps() {
		// create list with all available tools
		this.mTools = new ArrayList<ITool>();
		mTools.addAll(mOutputPlugins);
		mTools.addAll(mGeneratorPlugins);
		mTools.addAll(mAnalysisPlugins);

		// "reverse index", mapping plug-ids to actual tools
		// needed for processing plugin statements in toolchains
		for (ITool tool : mTools) {
			this.mIdToTool.put(tool.getPluginID(), tool);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore#makeToolSelection
	 * ()
	 */
	@Override
	public Toolchain makeToolSelection() {

		if (mTools.isEmpty()) {
			mLogger.warn("There are no plugins present, returning null tools.");
			return null;
		}

		// present selection dialog
		Toolchain tmp = mCurrentController.selectTools(mTools);
		if (tmp == null) {
			/* dialog was aborted */
			mLogger.warn("Dialog was aborted, returning null tools.");
			return null;
		}
		if (!checkToolchain(tmp.getToolchain().getPluginOrSubchain())) {
			mLogger.warn("Invalid toolchain selection, returning null tools.");
			return null;
		}

		mLogger.info("Returning lots of tools...");
		this.mCurrentToolchain = tmp;
		return this.mCurrentToolchain;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore#processToolchain
	 * (org.eclipse.core.runtime.IProgressMonitor)
	 */
	@Override
	public IStatus processToolchain(IProgressMonitor monitor) throws Throwable {
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
			mCurrentToolchainMonitor = monitor;
			mToolchainWalker.walk(monitor);
			mCurrentToolchain.clearStore();
		} finally {
			if (useBenchmark) {
				bench.stopAll();
				mLogger.info("--------------------------------------------------------------------------------");
				bench.report();
				mBenchmark.report();
				UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID,
						new BenchmarkResult<Double>(Activator.s_PLUGIN_ID, "Toolchain Benchmarks", mBenchmark));
			}
			mLogger.info("--------------------------------------------------------------------------------");
			new ResultNotifier(mCurrentController).processResults();
			mModelManager.removeAll();
		}

		return Status.OK_STATUS;
	}

	private final IElement runParser(final File file, ISource parser) throws Exception {
		boolean useBenchmark = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getBoolean(CorePreferenceInitializer.LABEL_BENCHMARK);
		IElement root = null;
		// parse the files to Graph
		try {
			mLogger.info(String.format("Parsing single file: %s", file.getAbsolutePath()));
			if (useBenchmark) {
				mBenchmark.start(parser.getName());
			}
			root = parser.parseAST(file);
			if (useBenchmark) {
				mBenchmark.stop(parser.getName());
			}

			/*
			 * for testing purposes only for(ISerialization ser :
			 * m_SerializationPlugins) { ser.serialize(root, "c:\\test.txt");
			 * INode in = ser.deserialize("c:\\test.txt"); if(in == in)
			 * System.out.println(in.toString()); }
			 */
		} catch (Exception e) {
			mLogger.fatal("Parsing gives Exception", e);
			resetModelManager();
		}
		return root;
	}

	private final ISource selectParser(final File files) {

		// how many parsers does m_SourcePlugins provide?
		ArrayList<ISource> usableParsers = new ArrayList<ISource>();
		ISource parser = null;

		mLogger.debug("We have " + mSourcePlugins.size() + " parsers present.");

		// how many of these parsers can be used on our input file?
		for (ISource p : mSourcePlugins) {
			if (p.parseable(files)) {
				mLogger.info("Parser " + p.getName() + " is usable.");
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
			// otherwise use parser choosing mechanism provided by Controller
			parser = mCurrentController.selectParser(usableParsers);
		}

		return parser;
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

	public void stop() {
		mLogger.warn("Received 'Stop'-Command, ignoring...");
	}

	/**
	 * getter for field m_ActiveControllerId
	 * 
	 * @return the m_ActiveControllerId
	 */
	public String getActiveControllerId() {
		if (this.mCurrentController == null) {
			return Activator.s_PLUGIN_ID;
		}
		return this.mCurrentController.getPluginID();
	}

	/**
	 * getter for field m_StoredToolchainUse
	 * 
	 * @return the m_StoredToolchainUse
	 */
	public Toolchain getStoredToolchainUse() {
		return this.mCurrentToolchain;
	}

	/**
	 * getter for field m_allTools
	 * 
	 * @return the m_allTools
	 */
	public ArrayList<ITool> getAllTools() {
		return this.mTools;
	}

	/**
	 * Some getters that are only relevant for ToolchainWalker.
	 */

	protected Toolchain getToolchain() {
		return this.mCurrentToolchain;
	}

	protected IController getController() {
		return this.mCurrentController;
	}

	protected ISource getParser() {
		return this.mCurrentParser;
	}

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
				if (!mIdToTool.containsKey(plugin.getId())) {
					mLogger.error("Did not find plugin with id \"" + plugin.getId() + "\". Skipping execution...");
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

	@Override
	public boolean canRerun() {
		return mCurrentToolchain != null;
	}

	@Override
	public boolean hasInputFiles() {
		return mCurrentFiles != null;
	}

	@Override
	public void setToolchain(Toolchain toolchain) {
		mCurrentToolchain = toolchain;
	}

	@Override
	public void loadPreferences(String absolutePath) {
		loadPreferencesInternal(absolutePath);
	}

	private void loadPreferencesInternal(String filename) {

		if (filename != null && !filename.isEmpty()) {
			mLogger.debug("--------------------------------------------------------------------------------");
			mLogger.info("Loading settings from " + filename);
			try {
				FileInputStream fis = new FileInputStream(filename);
				IStatus status = UltimatePreferenceStore.importPreferences(fis);
				if (!status.isOK()) {
					mLogger.warn("Failed to load preferences. Status is: " + status);
					mLogger.warn("Did not attach debug property logger");
				} else {
					checkPreferencesForActivePlugins();
					mLogger.info("Loading preferences was successful");

				}
			} catch (Exception e) {
				mLogger.error("Could not load preferences because of exception: ", e);
				mLogger.warn("Did not attach debug property logger");
			} finally {
				mLogger.debug("--------------------------------------------------------------------------------");
			}

		} else {
			mLogger.info("Loading settings from empty filename is not possible");
		}
	}

	@Override
	public void savePreferences(String filename) {
		if (filename != null && !filename.isEmpty() && !mTools.isEmpty()) {
			mLogger.info("Saving preferences to file " + filename);
			try {
				File f = new File(filename);
				if (f.isFile() && f.exists()) {
					f.delete();
				}
				FileOutputStream fis = new FileOutputStream(filename);

				for (IUltimatePlugin plugin : getPlugins()) {
					new UltimatePreferenceStore(plugin.getPluginID()).exportPreferences(fis);
				}

				fis.flush();
				fis.close();
			} catch (FileNotFoundException e) {
				mLogger.error("Saving preferences failed with exception: ", e);
			} catch (IOException e) {
				mLogger.error("Saving preferences failed with exception: ", e);
			} catch (CoreException e) {
				mLogger.error("Saving preferences failed with exception: ", e);
			}
		}
	}

	/**
	 * Return false iff cancellation of toolchain is requested or deadline is
	 * exceeded.
	 */
	public boolean continueProcessing() {
		boolean cancel = mCurrentToolchainMonitor.isCanceled() || System.currentTimeMillis() > mDeadline;
		if (cancel) {
			mLogger.debug("Tool knows that it should cancel! It called continueProcessing and received false.");
		}
		return !cancel;
	}

	public void setSubtask(String task) {
		mCurrentToolchainMonitor.subTask(task);
	}

	/**
	 * Set a time limit after which the toolchain should be stopped.
	 * 
	 * A convenient way of setting this deadline is using
	 * System.currentTimeMillis() + timelimit (in ms) as value right before
	 * calling start(...).
	 * 
	 * @param date
	 *            A date in the future (aka, the difference, measured in
	 *            milliseconds, between the current time and midnight, January
	 *            1, 1970 UTC) after which a running toolchain should be
	 *            stopped.
	 */
	public void setDeadline(long date) {
		if (System.currentTimeMillis() >= date) {
			mLogger.warn(String
					.format("Deadline was set to a date in the past, " + "effectively stopping the toolchain. "
							+ "Is this what you intended? Value of date was %,d", date));

		}
		mDeadline = date;
	}

	public void cancelToolchain() {
		mToolchainWalker.requestCancel();
	}

	public class LogPreferenceChangeListener implements IPreferenceChangeListener {

		private String mScope;
		private String mPluginID;
		private UltimatePreferenceStore mPreferences;
		private String mPrefix;

		public LogPreferenceChangeListener(String scope, String pluginID) {
			mScope = scope;
			mPluginID = pluginID;
			mPreferences = new UltimatePreferenceStore(mPluginID);
			mPrefix = "[" + mPluginID + " (" + mScope + ")] Preference \"";
		}

		@Override
		public void preferenceChange(PreferenceChangeEvent event) {
			mLogger.debug(mPrefix + event.getKey() + "\" changed: " + event.getOldValue() + " -> "
					+ event.getNewValue() + " (actual value in store: " + mPreferences.getString(event.getKey()) + ")");
		}
	}

	@Override
	public IUltimatePlugin[] getPlugins() {
		ArrayList<IUltimatePlugin> rtr = new ArrayList<IUltimatePlugin>();
		rtr.addAll(mTools);
		rtr.addAll(mSourcePlugins);
		rtr.add(this);
		rtr.add(mCurrentController);
		return rtr.toArray(new IUltimatePlugin[rtr.size()]);
	}

	@Override
	public String getName() {
		return Activator.s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new CorePreferenceInitializer();
	}

	private void cleanup() {
		// we should provide a method for the external execution mode to release
		// all external resources acquired through an ultimate run

		UltimateServices.getInstance().terminateExternalProcesses();

	}

	@Override
	public CommandLineParser getCommandLineArguments() {
		return mCmdLineArgs;
	}

}
