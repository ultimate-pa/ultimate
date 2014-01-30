package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import javax.xml.bind.JAXBException;

import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;
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
import org.xml.sax.SAXException;

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
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ILoggingWindow;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.logging.UltimateLoggerFactory;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IModelManager;
import de.uni_freiburg.informatik.ultimate.model.PersistenceAwareModelManager;
import de.uni_freiburg.informatik.ultimate.model.repository.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.plugins.ResultNotifier;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;

/**
 * This class controls all aspects of the application's execution. This class
 * needs complete refactoring, perhaps even rewrite from scratch - DD
 * 
 * @author Jakob, Dietsch, Bjoern Buchhold, Christian Simon
 */
public class UltimateCore implements IApplication, ICore, IRCPPlugin {

	/**
	 * In what mode is Ultimate supposed tu run? With a GUI? With an interactive
	 * console? Or a fall-back command-line?
	 */
	public static enum Ultimate_Mode {
		/**
		 * This mode starts Ultimate with the GUI.
		 */
		USEGUI,
		/**
		 * This mode starts Ultimate with the Interactive Console. Which is
		 * basically a simple console application.
		 */
		INTERACTIVE,
		/**
		 * This mode starts Ultimate only with the given CmdLineArgs, there is
		 * no interaction with the user.
		 */
		FALLBACK_CMDLINE,
		/**
		 * This mode starts Ultimate with special parameters, which can be set
		 * in every instance. This mode is basically needed to start Ultimate
		 * from the Web-Server and the CDT-Plugin
		 */
		EXTERNAL_EXECUTION
	}

	private Ultimate_Mode mCoreMode;

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
	/**
	 * Only for EXTERNAL_EXECUTION mode.
	 */
	private File mToolchainXML;
	/**
	 * Only for EXTERNAL_EXECUTION mode.
	 */
	private File mSettingsFile;
	/**
	 * Only for EXTERNAL_EXECUTION mode.
	 */
	private File mInputFile;
	/**
	 * Only for EXTERNAL_EXECUTION mode.
	 */
	private Object mParsedAST;

	private HashMap<String, LogPreferenceChangeListener> mActivePreferenceListener;

	/**
	 * This Default-Constructor is needed to start up the application
	 */
	public UltimateCore() {

	}

	/**
	 * This constructor should only be used by the CDTPlugin and the WebServer
	 * 
	 * @param mode
	 *            the execution mode.
	 */
	public UltimateCore(UltimateCore.Ultimate_Mode mode) {
		if (mode != UltimateCore.Ultimate_Mode.EXTERNAL_EXECUTION) {
			throw new IllegalArgumentException("We expect EXTERNAL_EXECUTION mode here!");
		}
		this.mCoreMode = mode;
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

		if (mCoreMode == Ultimate_Mode.EXTERNAL_EXECUTION) {
			init();

			// throwing classes exported by plugins into arraylists
			loadExtension();

			// initialize the tools map
			initiateToolMaps();

			if (mSettingsFile != null) {
				loadPreferencesInternal(mSettingsFile.getPath());
			}

			// run previously chosen command line controller
			Object returnCode = mCurrentController.init(this);
			mLogger.info("Exiting Ultimate with returncode " + returnCode);

			// before we quit Ultimate, do we have to clear the model store?
			boolean store_mm = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
					.getBoolean(CorePreferenceInitializer.LABEL_MM_DROP_MODELS);
			if (store_mm) {
				for (String s : this.mModelManager.getItemNames()) {
					this.mModelManager.removeItem(s);
				}
			}

			cleanup();
			// this must be returned
			return IApplication.EXIT_OK;
		}
		// parser command line parameters
		mCmdLineArgs = new CommandLineParser();
		mCmdLineArgs.parse(Platform.getCommandLineArgs());

		// determine Ultimate's mode
		if (mCmdLineArgs.getInteractiveSwitch()) {
			this.mCoreMode = Ultimate_Mode.INTERACTIVE;
		} else if (mCmdLineArgs.getExitSwitch()) {
			mCmdLineArgs.printUsage();
			return IApplication.EXIT_OK;
		} else if (!mCmdLineArgs.getConsoleSwitch()) {
			this.mCoreMode = Ultimate_Mode.USEGUI;
		} else if (mCmdLineArgs.getConsoleSwitch()) {
			this.mCoreMode = Ultimate_Mode.FALLBACK_CMDLINE;
		}

		// if you need to debug the commandline...
		// m_CmdLineArgs.printUsage();

		// initializing variables, loggers,...
		init();

		// throwing classes exported by plugins into arraylists
		loadExtension();

		// initialize the tools map
		initiateToolMaps();

		String settingsfile = mCmdLineArgs.getSettings();
		if (settingsfile != null) {
			loadPreferencesInternal(settingsfile);
		}

		// at this point a gui or a cmd line controller may already be set.
		// if no controller is set, the default cmd line controller
		// without interactive mode is used as a fallback
		if (this.mCoreMode == Ultimate_Mode.USEGUI && mCurrentController != null) {
			this.initializeGUI();
		} else if (mCurrentController != null) {
			// run previously chosen command line controller
			Object returnCode = mCurrentController.init(this);
			mLogger.info("Preparing to exit Ultimate with return code " + returnCode);
		}

		// before we quit Ultimate, do we have to clear the model store?
		boolean store_mm = new UltimatePreferenceStore(Activator.s_PLUGIN_ID).getBoolean(
				CorePreferenceInitializer.LABEL_MM_DROP_MODELS, true);
		if (store_mm) {
			for (String s : this.mModelManager.getItemNames()) {
				this.mModelManager.removeItem(s);
			}
		}
		// this must be returned
		cleanup();
		return IApplication.EXIT_OK;
	}

	private void initializeGUI() {
		mLogger.info("Initializing GUI ...");
		if (mCurrentController == null) {
			mLogger.fatal("No GUI controller present although initializeGUI() was called !");
			throw new NullPointerException("No GUI controller present although initializeGUI() was called !");
		}
		loadGuiLoggingWindow(Platform.getExtensionRegistry());
		Object returnCode = mCurrentController.init(this);
		mLogger.info("Preparing to exit Ultimate with return code " + returnCode);
	}

	/**
	 * Initialization of private variables. Configures the Logging Subsystem and
	 * adds the first appender. this function must be called before the first
	 * usage of the logging subsystem
	 * 
	 */
	private void init() {
		UltimateServices.createInstance(this);

		// Here we set the parsed AST for the cdt plugin
		UltimateServices.getInstance().setParsedAST(mParsedAST);

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
		mBenchmark = new Benchmark();
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
			mLogger.warn("CurrentController is null (CurrentMode: " + mCoreMode + ")");
		} else {
			attachLogPreferenceChangeListenerToPlugin(mCurrentController.getPluginID());
			logDefaultPreferences(mCurrentController.getPluginID());
		}

		for (IRCPPlugin t : mOutputPlugins) {
			attachLogPreferenceChangeListenerToPlugin(t.getPluginID());
			logDefaultPreferences(t.getPluginID());
		}
		for (IRCPPlugin t : mSourcePlugins) {
			attachLogPreferenceChangeListenerToPlugin(t.getPluginID());
			logDefaultPreferences(t.getPluginID());
		}
		for (IRCPPlugin t : mGeneratorPlugins) {
			attachLogPreferenceChangeListenerToPlugin(t.getPluginID());
			logDefaultPreferences(t.getPluginID());
		}

		for (IRCPPlugin t : mAnalysisPlugins) {
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
	 */
	private void loadExtension() {
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
	 */
	private void loadControllerPlugins(IExtensionRegistry reg) {

		boolean usegui = false;
		if (this.mCoreMode == Ultimate_Mode.USEGUI) {
			usegui = true;
		}

		IConfigurationElement[] configElements_ctr = reg.getConfigurationElementsFor(ExtensionPoints.EP_CONTROLLER);

		// create list of controllers that fulfill the desired GUI property (gui
		// / nogui)
		List<IConfigurationElement> suitableControllers = new LinkedList<IConfigurationElement>();
		for (int i = 0; i < configElements_ctr.length; i++) {
			String attr = configElements_ctr[i].getAttribute("isGraphical");
			if (attr != null && new Boolean(attr).equals(usegui)) {
				suitableControllers.add(configElements_ctr[i]);
			}
		}

		if (usegui) {
			mLogger.info("Getting present graphical controllers (" + suitableControllers.size() + ")");
		} else {
			mLogger.info("Getting present non-graphical controllers (" + suitableControllers.size() + ")");
		}

		try {

			this.mCurrentController = chooseController(suitableControllers);

		} catch (FileNotFoundException e) {
			mLogger.error("The specified file " + e.getMessage() + " was not found or couldn't be read.");
			this.mCmdLineArgs.printUsage();
			mLogger.info("Exiting Ultimate.");
		} catch (JAXBException e) {
			mLogger.error("There was an error processing the XML file. Please make sure that it validates against toolchain.xsd.");
			mLogger.info("Exiting Ultimate.");
		} catch (SAXException e) {
			mLogger.error("There was an error parsing the XML file. Please make sure that it validates against toolchain.xsd.");
			mLogger.info("Exiting Ultimate.");
		}

	}

	/**
	 * Choose a controller compliant with the user's desire. If the commandline
	 * controller is desired, an instance will be returned. If the interactive
	 * controller is desired, an instance of it will be returned. If only one
	 * gui controller is present, this very one will be returned if Ultimate is
	 * in GUI mode. If more than one is present, a dialog will appear where the
	 * user may choose.
	 * 
	 * @param suitableControllers
	 *            All controllers that can be used.
	 * @return Controller chosen by the user or fallback controller.
	 * @throws FileNotFoundException
	 * @throws JAXBException
	 * @throws SAXException
	 */
	private IController chooseController(List<IConfigurationElement> suitableControllers) throws FileNotFoundException,
			JAXBException, SAXException {

		// for external execution we need a "special" controller
		if (this.mCoreMode == Ultimate_Mode.EXTERNAL_EXECUTION) {
			return new ExtExecutionController(this.mToolchainXML.getPath(), this.mInputFile);
		}

		// command-line controller desired, return it
		if (this.mCoreMode == Ultimate_Mode.FALLBACK_CMDLINE)
			return new CommandlineController(this.mCmdLineArgs);

		// if in interactive mode, search for suitable controller
		if (this.mCoreMode == Ultimate_Mode.INTERACTIVE) {
			for (IConfigurationElement element : suitableControllers) {

				// in interactive mode return interactive controller
				if (element.getAttribute("class").equals(
						"de.uni_freiburg.informatik.ultimate.interactiveconsole.InteractiveConsoleController"))
					try {

						return (IController) element.createExecutableExtension("class");
					} catch (CoreException e1) {
						mLogger.error("The desired controller for the interactive console could not be loaded!");
					}
			}
		}

		if (this.mCoreMode == Ultimate_Mode.USEGUI) {
			int availableControllersCount = suitableControllers.size();
			if (availableControllersCount == 1) {
				try {
					return (IController) (suitableControllers.get(0).createExecutableExtension("class"));
				} catch (CoreException e) {
					mLogger.error("The desired gui controller could not be loaded!");
				}
			} else if (availableControllersCount > 1) {
				// TODO remove the whole code when refactoring is complete
				// (every controller in its own plugin)
				// removed ControllerChooseDialog. It seems not necessary to be
				// able to choose between different controllers at runtime.
				// ControllerChooseDialog chooser = new ControllerChooseDialog(
				// suitableControllers);
				// int return_value = chooser.open();
				int return_value = 0;
				if (return_value >= 0) {
					try {
						return (IController) (suitableControllers.get(return_value).createExecutableExtension("class"));
					} catch (CoreException e) {
						mLogger.error("The desired gui controller could not be loaded!");
					}
				}
			} else {
				mLogger.error("CoreMode is USEGUI, but no usable GUI controller could be found.");
			}
		}

		mLogger.warn("Could not load a suitable controller. Falling back to default command line controller");
		return new CommandlineController(this.mCmdLineArgs);
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
				if (!(output.isGuiRequired() && this.mCoreMode != Ultimate_Mode.USEGUI))
					mOutputPlugins.add(output);
				else
					mLogger.error("Can't load a gui plugin in command-line mode!");
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
				if (!(generator.isGuiRequired() && this.mCoreMode != Ultimate_Mode.USEGUI)) {
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
				if (!(analysis.isGuiRequired() && this.mCoreMode != Ultimate_Mode.USEGUI))
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
				if (t != null)
					t.init(null);
			}
		} else {
			for (IOutput out : mOutputPlugins) {
				mLogger.info("Initializing " + out.getName() + "...");
				out.init(null);
			}
			for (IGenerator trans : mGeneratorPlugins) {
				mLogger.info("Initializing " + trans.getName() + "...");
				trans.init(null);
			}
			for (IAnalysis trans : mAnalysisPlugins) {
				mLogger.info("Initializing " + trans.getName() + "...");
				trans.init(null);
			}
		}
		for (ISource source : mSourcePlugins) {
			mLogger.info("Initializing " + source.getName() + "...");
			source.init(null);
		}

		mLogger.info("Finished initializing Plugins !");
		mLogger.info("--------------------------------------------------------------------------------");
	}

	/**
	 * method for loading the contributed logging window.. there is currently no
	 * distinction between loggign window.. as there is only one for the gui
	 * important .. no logging messsages should go to the gui logging window if
	 * the Gui is not up and running ...
	 * 
	 * this code is hard to be removed from the Application class because basic
	 * Features of the {@link UltimateLoggerFactory} have to be present before
	 * the GUI is loaded and even if the GUI isn't present at all.
	 * 
	 * Therefore the Application takes care of adding the appender to the root
	 * logger
	 * 
	 */
	private void loadGuiLoggingWindow(IExtensionRegistry reg) {
		// -- LoggingWindow-Extension Point --
		// receiving configuration elements (see exsd-files)
		// which define class name in element "impl"
		// and attribute "class".
		IConfigurationElement[] configElements_out = reg.getConfigurationElementsFor(ExtensionPoints.EP_LOGGINGWINDOW);
		// iterate through every config element
		for (IConfigurationElement element : configElements_out) {
			try {
				ILoggingWindow loggingWindow = (ILoggingWindow) element.createExecutableExtension("class");
				loggingWindow.init(null);
				// and add to plugin ArrayList
				loggingWindow.setLayout(new PatternLayout(new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
						.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)));

				// use the root logger to have this appender in all child
				// loggers
				Logger.getRootLogger().addAppender(loggingWindow);
				mLogger.info("Activated GUI Logging Window for Log4j Subsystem");
			} catch (CoreException e) {
				mLogger.error("Could not load the logging window", e);
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore#resetCore()
	 */
	@Override
	public void resetCore() {
		initializePlugins();
		resetMemoryManager();
		this.mBenchmark.reset();
		this.mToolchainWalker.reset();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore#setInputFiles
	 * (java.io.File[])
	 */
	@Override
	public void setInputFile(File files) {
		this.mCurrentFiles = files;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore#initiateParser
	 * (de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider)
	 */
	@Override
	public boolean initiateParser(PreludeProvider preludefile) {
		this.mCurrentParser = selectParser(this.mCurrentFiles);

		if (mCurrentParser == null) {
			mLogger.warn("Parser is NULL, aborting...");
			return false;
		}

		// set prelude file if present
		if (preludefile != null)
			this.mCurrentParser.setPreludeFile(preludefile.getPreludeFile());
		else
			this.mCurrentParser.setPreludeFile(null);

		if (this.mCurrentParser.getOutputDefinition() == null) {
			mLogger.fatal("ISource returned invalid Output Definition, aborting...");
			return false;
		}

		mLogger.info("Parser successfully initiated...");

		return true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore#letCoreRunParser
	 * ()
	 */
	@Override
	public void letCoreRunParser() throws Exception {
		boolean rtr_value = mModelManager.addItem(runParser(this.mCurrentFiles, this.mCurrentParser),
				this.mCurrentParser.getOutputDefinition());

		mLogger.debug("DataSafe ADD Operation successful: " + rtr_value);
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
	public IStatus processToolchain(IProgressMonitor monitor) throws Exception {

		Benchmark b = new Benchmark();
		b.start("Core");
		if (mModelManager.size() < 1) {
			mLogger.error("no model present, aborting...");
			throw new Exception("There is no model present");
		}
		mCurrentToolchainMonitor = monitor;
		mToolchainWalker.walk(monitor);
		new ResultNotifier(mCurrentController).processResults();
		mCurrentToolchain.clearStore();
		b.stopAll();
		mLogger.info(String.format("Finished toolchain execution after %.2f ms",
				b.getElapsedTime("Core", TimeUnit.MILLISECONDS)));
		mBenchmark.report();
		mLogger.info("--------------------------------------------------------------------------------");

		return Status.OK_STATUS;
	}

	private final IElement runParser(final File file, ISource parser) throws Exception {

		IElement root = null;
		// parse the files to Graph
		try {
			mLogger.info("Parsing single file ...");
			mBenchmark.start(parser.getName());
			root = parser.parseAST(file);
			mBenchmark.stop(parser.getName());

			/*
			 * for testing purposes only for(ISerialization ser :
			 * m_SerializationPlugins) { ser.serialize(root, "c:\\test.txt");
			 * INode in = ser.deserialize("c:\\test.txt"); if(in == in)
			 * System.out.println(in.toString()); }
			 */
		} catch (Exception e) {
			mLogger.fatal("Parsing gives Exception", e);
			resetMemoryManager();
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

	private void resetMemoryManager() {
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
	 * getter for field m_CoreMode
	 * 
	 * @return the m_CoreMode
	 */
	public Ultimate_Mode getCoreMode() {
		return this.mCoreMode;
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
	public void loadPreferences() {
		loadPreferencesInternal(mCurrentController.getLoadPrefName());
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
	public void savePreferences() {
		String filename = mCurrentController.getSavePrefName();
		if (filename != null && !filename.isEmpty() && !mTools.isEmpty()) {
			mLogger.info("Saving preferences to file " + filename);
			try {
				FileOutputStream fis = new FileOutputStream(filename);

				for (IRCPPlugin plugin : getPlugins()) {
					new UltimatePreferenceStore(plugin.getPluginID()).exportPreferences(fis);
				}

				fis.flush();
				fis.close();
			} catch (FileNotFoundException e) {
				mLogger.warn("Saving preferences failed with exception: ", e);
			} catch (IOException e) {
				mLogger.warn("Saving preferences failed with exception: ", e);
			} catch (CoreException e) {
				mLogger.warn("Saving preferences failed with exception: ", e);
			}
		}

		// old variant:
		// String filename = mCurrentController.getSavePrefName();
		// if (filename != null && !filename.isEmpty() && !mTools.isEmpty()) {
		// String toolName = "";
		// try {
		// FileOutputStream fis = new FileOutputStream(filename);
		// IPreferencesService ps = Platform.getPreferencesService();
		// IScopeContext cs = ConfigurationScope.INSTANCE;
		// IScopeContext is = InstanceScope.INSTANCE;
		// ps.exportPreferences(cs.getNode(Activator.s_PLUGIN_ID), fis,
		// null);
		// ps.exportPreferences(is.getNode(Activator.s_PLUGIN_ID), fis,
		// null);
		//
		// for (ITool tool : mTools) {
		// toolName = tool.getName();
		// mLogger.debug("Saving preferences for tool " + toolName
		// + " ...");
		// IEclipsePreferences[] prefs = tool.getPreferences(cs, is);
		// if (prefs != null) {
		// for (IEclipsePreferences p : prefs) {
		// ps.exportPreferences(p, fis, null);
		// }
		// }
		// }
		// fis.flush();
		// fis.close();
		// } catch (Exception e) {
		// mLogger.warn("Saving preferences failed at " + toolName
		// + " with exception: ", e);
		// }
		// }
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

	/**
	 * @return the m_ToolchainXML
	 */
	public File getToolchainXML() {
		return mToolchainXML;
	}

	/**
	 * @param m_ToolchainXML
	 *            the m_ToolchainXML to set
	 */
	public void setToolchainXML(File m_ToolchainXML) {
		this.mToolchainXML = m_ToolchainXML;
	}

	/**
	 * @return the m_SettingsFile
	 */
	public File getSettingsFile() {
		return mSettingsFile;
	}

	/**
	 * @param m_SettingsFile
	 *            the m_SettingsFile to set
	 */
	public void setSettingsFile(File m_SettingsFile) {
		this.mSettingsFile = m_SettingsFile;
	}

	/**
	 * @return the m_InputFile
	 */
	public File getInputFile() {
		return mInputFile;
	}

	/**
	 * @param m_InputFile
	 *            the m_InputFile to set
	 */
	public void setM_InputFile(File m_InputFile) {
		this.mInputFile = m_InputFile;
	}

	/**
	 * @return the m_ParsedAST
	 */
	public Object getParsedAST() {
		return mParsedAST;
	}

	/**
	 * @param m_ParsedAST
	 *            the m_ParsedAST to set
	 */
	public void setM_ParsedAST(Object m_ParsedAST) {
		this.mParsedAST = m_ParsedAST;
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
	public IRCPPlugin[] getPlugins() {
		ArrayList<IRCPPlugin> rtr = new ArrayList<IRCPPlugin>();
		rtr.addAll(mTools);
		rtr.addAll(mSourcePlugins);
		rtr.add(this);
		rtr.add(mCurrentController);
		return rtr.toArray(new IRCPPlugin[rtr.size()]);
	}

	@Override
	public int init(Object params) {
		throw new UnsupportedOperationException("The core does not initialize itself");
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

}
