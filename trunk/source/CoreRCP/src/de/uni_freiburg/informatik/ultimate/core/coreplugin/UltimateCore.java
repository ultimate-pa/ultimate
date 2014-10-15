package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.LoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin;

/**
 * This class controls all aspects of the application's execution.
 * 
 * @author dietsch
 */
public class UltimateCore implements IApplication, ICore, IUltimatePlugin {

	// TODO: Remove de.uni_freiburg.informatik.ultimate.core.coreplugin from
	// exported packages

	private Logger mLogger;

	private IController mCurrentController;

	/**
	 * What arguments were passed to the Ultimate RCP product before start-up?
	 */
	private CommandLineParser mCmdLineArgs;

	private ToolchainWalker mToolchainWalker;

	private ToolchainStorage mCoreStorage;

	private PluginFactory mPluginFactory;

	private SettingsManager mSettingsManager;

	private ToolchainManager mToolchainManager;

	private LoggingService mLoggingService;

	private JobChangeAdapter mJobChangeAdapter;

	/**
	 * This Default-Constructor is needed to start up the application
	 */
	public UltimateCore() {

	}

	public final Object start(IController controller, boolean isGraphical) throws Exception {
		setCurrentController(controller);
		return start(null);
	}

	/**
	 * Delegates control to the controller.
	 * 
	 * @return Ultimate's exit code.
	 */
	private int activateController() {
		mLogger.info("Initializing controller ...");
		if (getCurrentController() == null) {
			mLogger.fatal("No controller present! Ultimate will exit.");
			throw new NullPointerException("No controller present!");
		}
		// TODO: Find better way than this cast
		mLoggingService.setCurrentControllerID(getCurrentControllerID());
		int returnCode = getCurrentController().init(this, mLoggingService);
		mLogger.info("Preparing to exit Ultimate with return code " + returnCode);
		return returnCode;
	}

	public void cancelToolchain() {
		mToolchainWalker.cancelToolchain();
	}

	/***************************** ICore Implementation *********************/

	@Override
	public IUltimatePlugin[] getRegisteredUltimatePlugins() {
		ArrayList<IUltimatePlugin> rtr = new ArrayList<IUltimatePlugin>();
		rtr.addAll(mPluginFactory.getAllAvailableToolchainPlugins());
		rtr.add(this);
		rtr.add(getCurrentController());
		return rtr.toArray(new IUltimatePlugin[rtr.size()]);
	}

	@Override
	public String[] getRegisteredUltimatePluginIDs() {
		List<String> rtr = mPluginFactory.getPluginIds();
		return rtr.toArray(new String[rtr.size()]);
	}

	@Override
	public CommandLineParser getCommandLineArguments() {
		return mCmdLineArgs;
	}

	@Override
	public void loadPreferences(String absolutePath) {
		mSettingsManager.loadPreferencesFromFile(absolutePath);
	}

	@Override
	public void savePreferences(String filename) {
		if (filename != null && !filename.isEmpty()) {
			mLogger.info("Saving preferences to file " + filename);
			try {
				File f = new File(filename);
				if (f.isFile() && f.exists()) {
					f.delete();
				}
				FileOutputStream fis = new FileOutputStream(filename);

				for (IUltimatePlugin plugin : getRegisteredUltimatePlugins()) {
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

	@Override
	public IToolchain requestToolchain() {
		return mToolchainManager.requestToolchain();
	}

	@Override
	public void releaseToolchain(IToolchain toolchain) {
		mToolchainManager.releaseToolchain(toolchain);

	}

	/***************************** IUltimatePlugin Implementation *********************/
	@Override
	public String getPluginName() {
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

	/***************************** IApplication Implementation *********************/

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
		mCoreStorage = new ToolchainStorage();
		mLoggingService = (LoggingService) mCoreStorage.getLoggingService();
		mLogger = mLoggingService.getLogger(Activator.s_PLUGIN_ID);
		mLogger.info("Initializing application");

		final Logger tmpLogger = mLogger;
		mJobChangeAdapter = new JobChangeAdapter() {

			@Override
			public void done(IJobChangeEvent event) {
				if (event.getResult().getException() != null) {
					tmpLogger.error("Error during toolchain job processing:", event.getResult().getException());
					if (Platform.inDebugMode() || Platform.inDevelopmentMode()) {
						event.getResult().getException().printStackTrace();
					}
				}
			}

		};
		Job.getJobManager().addJobChangeListener(mJobChangeAdapter);
		mLogger.info("--------------------------------------------------------------------------------");

		// loading classes exported by plugins
		mSettingsManager = new SettingsManager(mLogger);

		mSettingsManager.checkPreferencesForActivePlugins(getPluginID(), getPluginName());

		mPluginFactory = new PluginFactory(mSettingsManager, mLogger);
		setCurrentController(mPluginFactory.getController());

		mToolchainManager = new ToolchainManager(mLoggingService, mPluginFactory, getCurrentController());

		String settingsfile = mCmdLineArgs.getSettings();
		if (settingsfile != null) {
			mSettingsManager.loadPreferencesFromFile(settingsfile);
		}

		try {
			// at this point a controller is already selected. We delegate
			// control
			// to this controller.
			Object rtrCode = activateController();

			// Ultimate is closing here
			mToolchainManager.close();
			return rtrCode;
		} finally {
			// we have to ensure that the JobChangeAdapter is properly removed,
			// because he implicitly holds references to UltimateCore and may
			// produce memory leaks
			Job.getJobManager().removeJobChangeListener(mJobChangeAdapter);
			mJobChangeAdapter = null;
		}
	}

	@Override
	public void stop() {
		mLogger.warn("Received 'Stop'-Command, ignoring...");
	}

	/***************************** Getters & Setters *********************/

	private void setCurrentController(IController controller) {
		if (mCurrentController != null) {
			if (controller == null) {
				mLogger.warn("Controller already set! Using " + mCurrentController.getPluginName()
						+ " and ignoring request to set controller to NULL (this may indicate test mode!)");
			} else {
				mLogger.warn("Controller already set! Using " + mCurrentController.getPluginName()
						+ " and ignoring request to set " + controller.getPluginName());
			}
			return;
		}
		assert controller != null;
		mCurrentController = controller;
	}

	private IController getCurrentController() {
		return mCurrentController;
	}

	private String getCurrentControllerID() {
		if (getCurrentController() == null) {
			return Activator.s_PLUGIN_ID;
		}
		return getCurrentController().getPluginID();
	}

	private static String[] sPluginNames;

	public static String[] getPluginNames() {
		if (sPluginNames == null) {
			List<String> lil = new ArrayList<>();
			for (String ep : ExtensionPoints.PLUGIN_EPS) {
				for (IConfigurationElement elem : Platform.getExtensionRegistry().getConfigurationElementsFor(ep)) {
					String classname = elem.getAttribute("class");
					lil.add(classname.substring(0, classname.lastIndexOf(".")));
				}
			}
			sPluginNames = lil.toArray(new String[0]);
		}
		return sPluginNames;
	}

}
