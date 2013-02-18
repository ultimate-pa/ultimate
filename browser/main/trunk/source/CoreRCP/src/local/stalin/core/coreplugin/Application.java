package local.stalin.core.coreplugin;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import javax.xml.bind.JAXBException;
import local.stalin.core.api.PreludeProvider;
import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.preferences.IPreferenceConstants;
import local.stalin.core.coreplugin.toolchain.PluginType;
import local.stalin.core.coreplugin.toolchain.SubchainType;
import local.stalin.core.coreplugin.toolchain.Toolchain;
import local.stalin.ep.ExtensionPoints;
import local.stalin.ep.interfaces.IAnalysis;
import local.stalin.ep.interfaces.IController;
import local.stalin.ep.interfaces.ICore;
import local.stalin.ep.interfaces.IGenerator;
import local.stalin.ep.interfaces.ILoggingWindow;
import local.stalin.ep.interfaces.IOutput;
import local.stalin.ep.interfaces.ISerialization;
import local.stalin.ep.interfaces.ISource;
import local.stalin.ep.interfaces.ITool;
import local.stalin.logging.StalinLoggerFactory;

import local.stalin.model.IModelManager;
import local.stalin.model.INode;
import local.stalin.model.PersistenceAwareModelManager;
import local.stalin.model.repository.StoreObjectException;
import local.stalin.plugins.Constants;

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
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IPreferencesService;
import org.eclipse.core.runtime.preferences.IScopeContext;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.xml.sax.SAXException;

/**
 * This class controls all aspects of the application's execution. This class
 * needs complete refactoring, perhaps even rewrite from scratch - DD
 * 
 * @author Jakob, Dietsch, Bjoern Buchhold, Christian Simon
 */
public class Application implements IApplication, ICore {

	/**
	 * In what mode is Stalin supposed tu run?
	 * With a GUI? With an interactive console? 
	 * Or a fall-back command-line?
	 */
	public static enum Stalin_Mode { USEGUI,
	  	  INTERACTIVE,
	  	  FALLBACK_CMDLINE};
	
	
	/**
	 * Stalin's running mode
	 */
	private Stalin_Mode m_CoreMode; 
	  	  
	/**
	 * Log4j-Logger.
	 */
	private static Logger s_Logger;

	
	/**
	 * Array where all output plugins are hold.
	 */
	private ArrayList<IOutput> m_OutputPlugins;

	/**
	 * a collection where all transformer plugins are held
	 * 
	 */
	private ArrayList<IGenerator> m_GeneratorPlugins;

	/**
	 * a collection where all analysis plugins are held
	 * 
	 */
	private ArrayList<IAnalysis> m_AnalysisPlugins;

	/**
	 * a controller provided by some plug-in implementing
	 * the IController interface, or just the fall-back
	 * command-line controller
	 */
	private IController m_Controller;

	/**
	 * 
	 * a collection where all parser plugins are held.
	 */
	private ArrayList<ISource> m_SourcePlugins;

	/**
	 * 
	 * a collection where all parser plugins are held.
	 */
	private ArrayList<ISerialization> m_SerializationPlugins;

	/**
	 * the currently selected parser, 
	 * can be modified by public methods in ICore
	 */
	private ISource m_StoredParser;
	
	/**
	 * the currently selected boogie files,
	 * can also be modified by public methods in ICore
	 */
	private File m_StoredFiles;
	
	/**
	 * the currently active toolchain
	 * guess what: you can modify this one using a public
	 * method defined in ICore!
	 */
	private Toolchain m_StoredToolchainUse;

	/**
	 * a collection of all available tools
	 */
	private ArrayList<ITool> m_AllTools;
	
	/**
	 * the same content as m_AllTools, but 
	 * as a mapping of tool ids to the actual tools
	 */
	private HashMap<String, ITool> m_Id2Plugin;	

	private Benchmark m_Bench;
	
	/**
	 * the chamber is used to store all different modells of the framework. he
	 * should also provide save and load functions and is responisble for memory
	 * management
	 */
	private IModelManager m_ModelManager;
		
	/**
	 * What arguments were passed to the Stalin RCP product before start-up?
	 */
	private CommandLineParser m_CmdLineArgs;

	private ToolchainWalker m_ToolchainWalker;

	/**
	 * Method which is called by Eclipse framework. Compare to "main"-method.
	 * 
	 * @param context Eclipse application context.
	 * @return Should return IPlatformRunnable.EXIT_OK or s.th. similar.
	 * @see org.eclipse.core.runtime.IPlatformRunnable#run(java.lang.Object)
	 * @throws Exception
	 *             May throw any exception
	 */
	public final Object start(IApplicationContext context) throws Exception {

		// parser command line parameters
		m_CmdLineArgs = new CommandLineParser();
		m_CmdLineArgs.parse(Platform.getCommandLineArgs());

		// determine Stalin's mode
		if ( m_CmdLineArgs.getInteractiveSwitch()) {
			this.m_CoreMode = Stalin_Mode.INTERACTIVE;
		} else if (m_CmdLineArgs.getExitSwitch()) {
			m_CmdLineArgs.printUsage();
			return IApplication.EXIT_OK;
		} else if (!m_CmdLineArgs.getConsoleSwitch()) {
			this.m_CoreMode = Stalin_Mode.USEGUI;
		} else if (m_CmdLineArgs.getConsoleSwitch()) {
			this.m_CoreMode = Stalin_Mode.FALLBACK_CMDLINE;
		}
		
		//if you need to debug the commandline...
		//m_CmdLineArgs.printUsage();

		// initializing variables, loggers,...
		init();

		String settingsfile = m_CmdLineArgs.getSettings();
		if (settingsfile != null) {
			loadPreferencesInternal(settingsfile);
		}
		
		// throwing classes exported by plugins into arraylists
		loadExtension();
		
		//initialize the tools map
		initiateToolMaps();

		// at this point a gui or a cmd line controller may already be set.
		// if no controller is set, the default cmd line controller
		// without interactive mode is used as a fallback
		if (this.m_CoreMode == Stalin_Mode.USEGUI 
				&& m_Controller != null) {
			this.initializeGUI();
		} else if (m_Controller != null) {
			// run previously chosen command line controller
			Object returnCode = m_Controller.init(this);
			s_Logger.info("Exiting STALIN with returncode " + returnCode);
		} 

		// before we quit Stalin, do we have to clear the model store?
		boolean store_mm = new InstanceScope().getNode(Activator.s_PLUGIN_ID).
			getBoolean(IPreferenceConstants.PREFID_MM_DROP_MODELS, true);
		if (store_mm) {
			for (String s: this.m_ModelManager.getItemNames()) {
				this.m_ModelManager.removeItem(s);
			}
		}
		
		// this must be returned
		return IApplication.EXIT_OK;
	}

	private void initializeGUI() {
		s_Logger.info("Initializing GUI ...");
		if (m_Controller == null) {
			s_Logger
					.fatal("No GUI controller present although initializeGUI() was called !");
			throw new NullPointerException(
					"No GUI controller present although initializeGUI() was called !");
		} else {
			loadGuiLoggingWindow(Platform.getExtensionRegistry());
			Object returnCode = m_Controller.init(this);
			s_Logger.info("Exiting STALIN with returncode " + returnCode);
		}
	}

	/**
	 * Initialization of private variables. Configures the Logging Subsystem and
	 * adds the first appender. this function must be called before the first
	 * usage of the logging subsystem
	 * 
	 */
	private void init() {
		StalinServices.createInstance(this);
		
		s_Logger = StalinServices.getInstance()
				.getLogger(Activator.s_PLUGIN_ID);

		s_Logger.info("Initializing application");
		
		// get tmp directory, use JAVA tmp dir by default
		String tmp_dir = new InstanceScope().getNode(Activator.s_PLUGIN_ID).
		get(IPreferenceConstants.PREFID_MM_TMPDIRECTORY, System.getProperty("java.io.tmpdir"));
		
		m_ModelManager = new PersistenceAwareModelManager(tmp_dir);
		m_OutputPlugins = new ArrayList<IOutput>();
		m_SourcePlugins = new ArrayList<ISource>();
		m_GeneratorPlugins = new ArrayList<IGenerator>();
		m_AnalysisPlugins = new ArrayList<IAnalysis>();
		m_SerializationPlugins = new ArrayList<ISerialization>();
		m_Id2Plugin = new HashMap<String, ITool>();
		m_StoredParser = null;
		m_StoredFiles = null;
		m_Bench = new Benchmark();
		// initialize walker with common variables
		m_ToolchainWalker = new ToolchainWalker(this, m_Bench, m_ModelManager, m_Id2Plugin);

		StalinServices.getInstance().setModelManager(m_ModelManager);
		final Logger tmp = s_Logger;
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
		s_Logger.info("--------------------------------------------------------------------------------");
		
	}

	/**
	 * Creates instances of plugin classes.
	 * 
	 */
	private void loadExtension() {
		IExtensionRegistry reg = Platform.getExtensionRegistry();
		s_Logger.info("Loading Plugins...");
		loadControllerPlugins(reg);
		loadOutputPlugins(reg);
		loadSourcePlugins(reg);
		loadSerializationPlugins(reg);
		loadGeneratorPlugins(reg);
		loadAnalysisPlugins(reg);
		s_Logger.info("Finished loading Plugins !");
		s_Logger.info("--------------------------------------------------------------------------------");
	}

	/**
	 * This method loads all contributions to the IController Extension Point.
	 * Its receiving configuration elements (see exsd-files) which define class
	 * name in element "impl" and attribute "class" as well as an attribute
	 * "isGraphical". It then
	 * 
	 * Changed in Stalin 2.0 to support multiple present controllers and to make
	 * the distinction between graphical and non graphical ones
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 */
	private void loadControllerPlugins(IExtensionRegistry reg) {
		
		boolean usegui = false;
		if (this.m_CoreMode == Stalin_Mode.USEGUI) {
			usegui = true;
		}
		
		IConfigurationElement[] configElements_ctr = reg
				.getConfigurationElementsFor(ExtensionPoints.EP_CONTROLLER);
		
		// create list of controllers that fulfill the desired GUI property (gui / nogui)
		List<IConfigurationElement> suitableControllers = new LinkedList<IConfigurationElement>();
		for (int i = 0; i < configElements_ctr.length; i++) {
			String attr = configElements_ctr[i].getAttribute("isGraphical");
			if (attr != null && new Boolean(attr).equals(usegui)) {
				suitableControllers.add(configElements_ctr[i]);
			}
		}
		
		if (usegui) {
			s_Logger.info("Getting present graphical controllers ("
					+ suitableControllers.size() + ")");
		} else {
			s_Logger.info("Getting present non-graphical controllers ("
					+ suitableControllers.size() + ")");
		}
		
		try {
			
			this.m_Controller = chooseController(suitableControllers);
			
		} catch (FileNotFoundException e) {
			s_Logger.error("The specified file "+e.getMessage()+" was not found or couldn't be read.");
			this.m_CmdLineArgs.printUsage();
			s_Logger.info("Exiting STALIN.");
		} catch (JAXBException e) {
			s_Logger.error("There was an error processing the XML file. Please make sure that it validates against toolchain.xsd.");
			s_Logger.info("Exiting STALIN.");
		} catch (SAXException e) {
			s_Logger.error("There was an error parsing the XML file. Please make sure that it validates against toolchain.xsd.");
			s_Logger.info("Exiting STALIN.");
		}

	}

	/**
	 * Choose a controller compliant with the user's desire.
	 * If the commandline controller is desired, an instance will
	 * be returned. If the interactive controller is desired, an
	 * instance of it will be returned. If only one gui controller
	 * is present, this very one will be returned if Stalin is in
	 * GUI mode. If more than one is present, a dialog will appear
	 * where the user may choose.
	 * 
	 * @param suitableControllers All controllers that can be used.
	 * @return Controller chosen by the user or fallback controller.
	 * @throws FileNotFoundException
	 * @throws JAXBException
	 * @throws SAXException 
	 */
	private IController chooseController(
			List<IConfigurationElement> suitableControllers) throws FileNotFoundException, JAXBException, SAXException {
		
		// command-line controller desired, return it
		if (this.m_CoreMode == Stalin_Mode.FALLBACK_CMDLINE)
			return new CommandlineController(this.m_CmdLineArgs);
		
		// if in interactive mode, search for suitable controller
		if (this.m_CoreMode == Stalin_Mode.INTERACTIVE) {
			for (IConfigurationElement element : suitableControllers) {
			
			// in interactive mode return interactive controller
			if (element.getAttribute("class").equals("local.stalin.interactiveconsole.InteractiveConsoleController"))
				try {
					
					return (IController) element.createExecutableExtension("class");
				} catch (CoreException e1) {
					s_Logger.error("The desired controller for the interactive console could not be loaded!");
				}
			}
		}
		
		if (this.m_CoreMode == Stalin_Mode.USEGUI) {
			if (suitableControllers.size() == 1) {
				try {
					return (IController) (suitableControllers.get(0).createExecutableExtension("class"));
				} catch (CoreException e) {
					s_Logger.error("The desired gui controller could not be loaded!");
				}
			} else {
				ControllerChooseDialog chooser = new ControllerChooseDialog(suitableControllers);
				int return_value = chooser.open();
				if (return_value >= 0) {
					try {
						return (IController) (suitableControllers.get(return_value).createExecutableExtension("class"));
					} catch (CoreException e) {
						s_Logger.error("The desired gui controller could not be loaded!");
					}
				}
			}
		}
		s_Logger.warn("Could not load a suitable controller. Falling back to default command line controller");
		return new CommandlineController(this.m_CmdLineArgs);
	}

	/**
	 * This method loads all contributions to the IOutput Extension Point. Its
	 * receiving configuration elements (see exsd-files) which define class name
	 * in element "impl" and attribute "class".
	 * If Stalin is not running in GUI mode, all plug-ins requiring a GUI will be
	 * omitted.
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 */
	private void loadOutputPlugins(IExtensionRegistry reg) {
		IConfigurationElement[] configElements_out = reg
				.getConfigurationElementsFor(ExtensionPoints.EP_OUTPUT);
		s_Logger.debug("We have " + configElements_out.length
				+ " possible Output plugin(s)");
		for (IConfigurationElement element : configElements_out) {
			try {
				IOutput output = (IOutput) element
						.createExecutableExtension("class");
				// skip gui plug-ins if not running in GUI mode
				if (!(output.isGuiRequired() && 
						this.m_CoreMode != Stalin_Mode.USEGUI))
					m_OutputPlugins.add(output);
				else s_Logger.error("Can't load a gui plugin in command-line mode!");
			} catch (CoreException e) {
				s_Logger.error("Can't load a Output Plugin !", e);
			}
		}
		s_Logger.info("Loaded " + m_OutputPlugins.size() + " Output Plugins");
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
		IConfigurationElement[] configElements_source = reg
				.getConfigurationElementsFor(ExtensionPoints.EP_SOURCE);
		s_Logger.debug("We have " + configElements_source.length
				+ " possible Source plugin(s)");
		for (IConfigurationElement element : configElements_source) {
			try {
				ISource source = (ISource) element
						.createExecutableExtension("class");
				m_SourcePlugins.add(source);
			} catch (CoreException e) {
				s_Logger.error("Can't load a Source Plugin !", e);
			}
		}
		s_Logger.info("Loaded " + m_SourcePlugins.size() + " Source Plugins");

	}

	/**
	 * This method loads all contributions to the ISerialization Extension
	 * Point. Its receiving configuration elements (see exsd-files) which define
	 * class name in element "impl" and attribute "class".
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 */
	private void loadSerializationPlugins(IExtensionRegistry reg) {
		IConfigurationElement[] configElements_serial = reg
				.getConfigurationElementsFor(ExtensionPoints.EP_SERIALIZATION);
		s_Logger.debug("We have " + configElements_serial.length
				+ " possible Serialization plugin(s)");
		for (IConfigurationElement element : configElements_serial) {
			try {
				ISerialization source = (ISerialization) element
						.createExecutableExtension("class");
				m_SerializationPlugins.add(source);
			} catch (CoreException e) {
				s_Logger.error("Can't load a Serialization Plugin ! ", e);
			}
		}
		s_Logger.info("Loaded " + m_SerializationPlugins.size()
				+ " Serialization Plugins");

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
		IConfigurationElement[] configElements_gen = reg
				.getConfigurationElementsFor(ExtensionPoints.EP_GENERATOR);
		for (IConfigurationElement element : configElements_gen) {
			try {
				IGenerator generator = (IGenerator) element
						.createExecutableExtension("class");
				// skip gui plug-ins if not running in GUI mode
				if (!(generator.isGuiRequired() && 
						this.m_CoreMode != Stalin_Mode.USEGUI))
					m_GeneratorPlugins.add(generator);
				else s_Logger.error("Can't load a gui plugin in command-line mode!");
			} catch (CoreException e) {
				s_Logger.error("Can't load a Generator Plugin !", e);
			}
		}
		s_Logger.info("Loaded " + m_GeneratorPlugins.size()
				+ " Generator Plugins");
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
		IConfigurationElement[] configElements_out = reg
				.getConfigurationElementsFor(ExtensionPoints.EP_ANALYSIS);
		s_Logger.debug("We have " + configElements_out.length
				+ " possible analysis plugin(s)");
		for (IConfigurationElement element : configElements_out) {
			try {
				IAnalysis analysis = (IAnalysis) element
						.createExecutableExtension("class");
				// skip gui plug-ins if not running in GUI mode
				if (!(analysis.isGuiRequired() && 
						this.m_CoreMode != Stalin_Mode.USEGUI))
					m_AnalysisPlugins.add(analysis);
				else s_Logger.error("Can't load a gui plugin in command-line mode!");
			} catch (CoreException e) {
				s_Logger.error("Can't load an analysis Plugin !", e);
			}
		}
		s_Logger.info("Loaded " + m_AnalysisPlugins.size()
				+ " analysis Plugins");
	}

	/**
	 * This method calls init methods of bound plugins.
	 * This is useful for the first loading of plug-ins
	 * and for re-initializing plug-ins that have been
	 * used in a toolchain.
	 */
	private void initializePlugins() {
		s_Logger.info("Initializing Plugins...");

		// re-initialize already opened plugins
		if (this.m_ToolchainWalker.getOpenPlugins().size() != 0) {
			for (String s: this.m_ToolchainWalker.getOpenPlugins().keySet()) {
				ITool t = m_Id2Plugin.get(s);
				if (t != null) 
					t.init(null);
			}
		}
		else {
		for (IOutput out : m_OutputPlugins) {
			s_Logger.info("Initializing " + out.getName() + "...");
			out.init(null);
		}
		for (IGenerator trans : m_GeneratorPlugins) {
			s_Logger.info("Initializing " + trans.getName() + "...");
			trans.init(null);
		}
		for (IAnalysis trans : m_AnalysisPlugins) {
			s_Logger.info("Initializing " + trans.getName() + "...");
			trans.init(null);
		}
		}
		for (ISource source : m_SourcePlugins) {
			s_Logger.info("Initializing " + source.getName() + "...");
			source.init(null);
		}
		for (ISerialization serialize : m_SerializationPlugins) {
			s_Logger.info("Initializing " + serialize.getName() + "...");
			serialize.init(null);
		}
		s_Logger.info("Finished initializing Plugins !");
		s_Logger.info("--------------------------------------------------------------------------------");
	}

	/**
	 * method for loading the contributed logging window.. there is currently no
	 * distinction between loggign window.. as there is only one for the gui
	 * important .. no logging messsages should go to the gui logging window if
	 * the Gui is not up and running ...
	 * 
	 * this code is hard to be removed from the Application class because basic
	 * Features of the {@link StalinLoggerFactory} have to be present before the
	 * GUI is loaded and even if the GUI isn't present at all.
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
		IConfigurationElement[] configElements_out = reg
				.getConfigurationElementsFor(ExtensionPoints.EP_LOGGINGWINDOW);
		// iterate through every config element
		for (IConfigurationElement element : configElements_out) {
			try {
				ILoggingWindow loggingWindow = (ILoggingWindow) element
						.createExecutableExtension("class");
				loggingWindow.init(null);
				// and add to plugin ArrayList
				loggingWindow.setLayout(new PatternLayout(Constants
						.getLoggerPattern()));

				// use the root logger to have this appender in all child
				// loggers
				Logger.getRootLogger().addAppender(loggingWindow);
				s_Logger
						.info("Activated GUI Logging Window for Log4j Subsystem");
			} catch (CoreException e) {
				s_Logger.error("Could not load the logging window", e);
			}
		}
	}

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ICore#resetCore()
	 */
	public void resetCore() {
		initializePlugins();
		resetMemoryManager();
		this.m_Bench.reset();
		this.m_ToolchainWalker.reset();
	}

	
	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ICore#setInputFiles(java.io.File[])
	 */
	public void setInputFile(File files) {
		this.m_StoredFiles = files;
	}

	
	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ICore#initiateParser(local.stalin.core.api.PreludeProvider)
	 */
	public boolean initiateParser(PreludeProvider preludefile) {
		this.m_StoredParser = selectParser(this.m_StoredFiles);

		if (m_StoredParser == null) {
			s_Logger.warn("Parser is NULL, aborting...");
			return false;
		}
		
		// set prelude file if present
		if (preludefile != null) 
			this.m_StoredParser.setPreludeFile(preludefile.getPreludeFile());
		else
			this.m_StoredParser.setPreludeFile(null);
		
		
		if (this.m_StoredParser.getOutputDefinition() == null) {
			s_Logger.fatal("ISource returned invalid Output Definition, aborting...");
			return false;
		}

		s_Logger.info("Parser successfully initiated...");

		return true;
	}

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ICore#letCoreRunParser()
	 */
	public void letCoreRunParser() throws Exception {
		boolean rtr_value = m_ModelManager
				.addItem(runParser(this.m_StoredFiles, this.m_StoredParser),
						this.m_StoredParser.getOutputDefinition());

		s_Logger.debug("DataSafe ADD Operation successful: " + rtr_value);
	}

	private void initiateToolMaps() {
		// create list with all available tools
		this.m_AllTools = new ArrayList<ITool>();
		m_AllTools.addAll(m_OutputPlugins);
		m_AllTools.addAll(m_GeneratorPlugins);
		m_AllTools.addAll(m_AnalysisPlugins);
		
		// "reverse index", mapping plug-ids to actual tools
		// needed for processing plugin statements in toolchains
		for (ITool tool : m_AllTools) {
			this.m_Id2Plugin.put(tool.getPluginID(), tool);
		}
	}

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ICore#makeToolSelection()
	 */
	public Toolchain makeToolSelection() {

		if (m_AllTools.isEmpty()) {
			s_Logger.warn("There are no plugins present, aborting...");
			return null;
		}

		// present selection dialog
		Toolchain tmp = m_Controller.selectTools(m_AllTools);
		if (tmp == null) {
			/* dialog was aborted */
			s_Logger.warn("Returning null tools...");
			return null;
		}
		if (!checkToolchain(tmp.getToolchain().getPluginOrSubchain())) {
			s_Logger.warn("Invalid toolchain selection...");
			return null;
		}

		s_Logger.info("Returning lots of  tools...");
		this.m_StoredToolchainUse = tmp;
		return this.m_StoredToolchainUse;
	}

		
	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ICore#processToolchain(org.eclipse.core.runtime.IProgressMonitor)
	 */
	public IStatus processToolchain(IProgressMonitor monitor) throws Exception {
				
		if (m_ModelManager.size() < 1) {
			s_Logger.error("no model present, aborting...");
			throw new Exception("There is no model present");
		}
		
		m_ToolchainWalker.walk(monitor);
		
        s_Logger.info("Finished executing Toolchain !");
        m_Bench.report();
        s_Logger.info("--------------------------------------------------------------------------------");
		
		return Status.OK_STATUS;
	}


	private final INode runParser(final File file, ISource parser)
			throws Exception {

		INode root = null;
		// parse the files to Graph
		try {
				s_Logger.info("Parsing single file ...");
				m_Bench.start("Parser");
				root = parser.parseAST(file);
				m_Bench.stop();
			
			/*
			 * for testing purposes only for(ISerialization ser :
			 * m_SerializationPlugins) { ser.serialize(root, "c:\\test.txt");
			 * INode in = ser.deserialize("c:\\test.txt"); if(in == in)
			 * System.out.println(in.toString()); }
			 */
		} catch (Exception e) {
			s_Logger.fatal("Parsing gives Exception", e);
			resetMemoryManager();
		}
		return root;
	}

	private final ISource selectParser(final File files) {

		// how many parsers does m_SourcePlugins provide?
		ArrayList<ISource> usableParsers = new ArrayList<ISource>();
		ISource parser = null;
		
		s_Logger.debug("We have " + m_SourcePlugins.size()
				+ " parsers present.");

		// how many of these parsers can be used on our input file?
		for (ISource p : m_SourcePlugins) {
			if (p.parseable(files)) {
				s_Logger.info("Parser " + p.getName() + " is usable.");
				usableParsers.add(p);
			}
		}


		boolean showusableparser = new ConfigurationScope().getNode(
				Activator.s_PLUGIN_ID).getBoolean(
				IPreferenceConstants.s_NAME_SHOWUSABLEPARSER, false);

		// if only parser can be used, choose it!
		if (usableParsers.size() == 1 && !showusableparser) {
			parser = usableParsers.get(0);
		} else if (usableParsers.isEmpty()) {
			return null;
		} else {
			// otherwise use parser choosing mechanism provided by Controller
			parser = m_Controller.selectParser(usableParsers);
		}

		return parser;
	}


	private void resetMemoryManager() {
		if (!m_ModelManager.isEmpty()) {
			s_Logger.info("Clearing model...");
			try {
				m_ModelManager.persistAll(false);
			} catch (StoreObjectException e) {
				s_Logger.error("Failed to persist Models", e);
			}
		}
		return;
	}

	public void stop() {
		s_Logger.warn("Received 'Stop'-Command, ignoring...");
	}

	/**
	 * getter for field m_ActiveControllerId
	 * 
	 * @return the m_ActiveControllerId
	 */
	public String getActiveControllerId() {
		if (this.m_Controller == null) {
			return Activator.s_PLUGIN_ID;
		}
		return this.m_Controller.getPluginID();
	}

	/**
	 * getter for field m_StoredToolchainUse
	 * @return the m_StoredToolchainUse
	 */
	public Toolchain getStoredToolchainUse() {
		return this.m_StoredToolchainUse;
	}

	/**
	 * getter for field m_allTools
	 * @return the m_allTools
	 */
	public ArrayList<ITool> getAllTools() {
		return this.m_AllTools;
	}

	/**
	 * getter for field m_CoreMode
	 * @return the m_CoreMode
	 */
	public Stalin_Mode getCoreMode() {
		return this.m_CoreMode;
	}

	/**
	 * Some getters that are only relevant
	 * for ToolchainWalker.
	 */
	
	protected Toolchain getToolchain() {
		return this.m_StoredToolchainUse;
	}
	
	protected IController getController() {
		return this.m_Controller;
	}

	protected ISource getParser() {
		return this.m_StoredParser;
	}
	
	/**
	 * Checks whether all plugins in the toolchain are present.
	 * @param chain Toolchain description to check.
	 * @return <code>true</code> if and only if every plugin in the chain
	 * 			exists.
	 */
	private boolean checkToolchain(List<Object> chain) {
		for (Object o : chain) {
			if (o instanceof PluginType) {
				PluginType plugin = (PluginType)o;
				if (!m_Id2Plugin.containsKey(plugin.getId())) {
					s_Logger.error("Did not find plugin with id \"" +
							plugin.getId() + "\". Skipping execution...");
					return false;
				}
			} else if (o instanceof SubchainType) {
				SubchainType sub = (SubchainType)o;
				if (!checkToolchain(sub.getPluginOrSubchain()))
					// Did already log...
					return false;
			}
		}
		return true;
	}

	@Override
	public boolean canRerun() {
		return m_StoredToolchainUse != null;
	}

	@Override
	public boolean hasInputFiles() {
		return m_StoredFiles != null;
	}

	@Override
	public void setToolchain(Toolchain toolchain) {
		m_StoredToolchainUse = toolchain;
	}

	@Override
	public void loadPreferences() {
		loadPreferencesInternal(m_Controller.getLoadPrefName());
	}
	
	private void loadPreferencesInternal(String filename) {
		if (filename != null && !filename.isEmpty()) {
			try {
				FileInputStream fis = new FileInputStream(filename);
				if (!Platform.getPreferencesService().importPreferences(fis).isOK())
					s_Logger.warn("Failed to load preferences");
			} catch (Exception e) {
				s_Logger.warn("Could not load preferences",e);
			}
		}
	}

	@Override
	public void savePreferences() {
		String filename = m_Controller.getSavePrefName();
		if (filename != null && !filename.isEmpty() && !m_AllTools.isEmpty()) {
			try {
				FileOutputStream fis = new FileOutputStream(filename);
				IPreferencesService ps = Platform.getPreferencesService();
				IScopeContext cs = new ConfigurationScope();
				IScopeContext is = new InstanceScope();
				ps.exportPreferences(cs.getNode(Activator.s_PLUGIN_ID), fis, null);
				ps.exportPreferences(is.getNode(Activator.s_PLUGIN_ID), fis, null);
				/*
				 * TODO This is a total hack, but I don't know right now how to
				 * save preferences for the SMTInterface...
				 */
				ps.exportPreferences(cs.getNode("SMTInterface"), fis, null);
				ps.exportPreferences(is.getNode("SMTInterface"), fis, null);
				for (ITool tool : m_AllTools) {
					IEclipsePreferences[] prefs = tool.getPreferences(cs,is);
					if (prefs != null) {
						for (IEclipsePreferences p : prefs)
							ps.exportPreferences(p,fis,null);
					}
				}
			} catch (Exception e) {
				s_Logger.warn("Could not load preferences",e);
			}
		}
	}

	@Override
	public void getAllPreferences() {
		// TODO Auto-generated method stub
		
	}
	
}
