/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.Log4JLoggingService;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainListType;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;

/**
 * This class controls all aspects of the application's execution.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class UltimateCore implements IApplication, ICore<ToolchainListType>, IUltimatePlugin {

	// TODO: Remove de.uni_freiburg.informatik.ultimate.core.model.coreplugin from
	// exported packages

	private static String[] sPluginNames;

	private ILogger mLogger;

	private IController<ToolchainListType> mCurrentController;

	private ToolchainWalker mToolchainWalker;

	private ToolchainStorage mCoreStorage;

	private PluginFactory mPluginFactory;

	private SettingsManager mSettingsManager;

	private ToolchainManager mToolchainManager;

	private Log4JLoggingService mLoggingService;

	private JobChangeAdapter mJobChangeAdapter;

	public UltimateCore() {
		// This Default-Constructor is needed to start up the application
	}

	public final Object startManually(final IController<ToolchainListType> controller) throws Exception {
		setCurrentController(controller);
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
	public final Object start(final IApplicationContext context) throws Exception {
		// initializing variables, loggers,...
		mCoreStorage = new ToolchainStorage();
		mLoggingService = mCoreStorage.getLoggingService();
		mLogger = mLoggingService.getLogger(Activator.PLUGIN_ID);
		mLogger.info("Initializing application");

		final ILogger tmpLogger = mLogger;
		mJobChangeAdapter = new UltimateJobChangeAdapter(tmpLogger);
		Job.getJobManager().addJobChangeListener(mJobChangeAdapter);
		mLogger.info("--------------------------------------------------------------------------------");

		// loading default settings
		mSettingsManager = new SettingsManager(mLogger);
		mSettingsManager.registerPlugin(this);

		// loading classes exported by plugins
		mPluginFactory = new PluginFactory(mSettingsManager, mLogger);
		setCurrentController(mPluginFactory.getController());

		mToolchainManager = new ToolchainManager(mLoggingService, mPluginFactory, getCurrentController());

		try {
			// at this point a controller is already selected. We delegate
			// control
			// to this controller.
			final Object rtrCode = activateController();

			// Ultimate is closing here
			mToolchainManager.close();
			return rtrCode;
		} finally {
			// we have to ensure that the JobChangeAdapter is properly removed,
			// because he implicitly holds references to UltimateCore and may
			// produce memory leaks
			Job.getJobManager().removeJobChangeListener(mJobChangeAdapter);
			mJobChangeAdapter = null;
			mCoreStorage.clear();
		}
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
			throw new IllegalArgumentException("No controller present!");
		}
		// TODO: Find better way than this cast
		mLoggingService.setCurrentControllerID(getCurrentControllerID());
		final int returnCode = getCurrentController().init(this);
		mLogger.info("Preparing to exit Ultimate with return code " + returnCode);
		return returnCode;
	}

	public void cancelToolchain() {
		mToolchainWalker.cancelToolchain();
	}

	/***************************** ICore Implementation *********************/

	@Override
	public IUltimatePlugin[] getRegisteredUltimatePlugins() {
		final List<IUltimatePlugin> rtr = new ArrayList<IUltimatePlugin>();
		rtr.addAll(mPluginFactory.getAllAvailableToolchainPlugins());
		rtr.add(this);
		rtr.add(getCurrentController());
		return rtr.toArray(new IUltimatePlugin[rtr.size()]);
	}

	@Override
	public String[] getRegisteredUltimatePluginIDs() {
		final List<String> rtr = mPluginFactory.getPluginIds();
		return rtr.toArray(new String[rtr.size()]);
	}

	@Override
	public void loadPreferences(final String absolutePath) {
		mSettingsManager.loadPreferencesFromFile(this, absolutePath);
		mLoggingService.refreshLoggingService();
	}

	@Override
	public void savePreferences(final String filename) {
		mSettingsManager.savePreferences(this, filename);
	}

	@Override
	public void resetPreferences() {
		mSettingsManager.resetPreferences(this);
	}

	@Override
	public IToolchain<ToolchainListType> requestToolchain() {
		return mToolchainManager.requestToolchain();
	}

	@Override
	public void releaseToolchain(final IToolchain<ToolchainListType> toolchain) {
		mToolchainManager.releaseToolchain(toolchain);

	}

	@Override
	public void stop() {
		mLogger.warn("Received 'Stop'-Command, ignoring...");
	}

	private void setCurrentController(final IController<ToolchainListType> controller) {
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

	private IController<ToolchainListType> getCurrentController() {
		return mCurrentController;
	}

	private String getCurrentControllerID() {
		if (getCurrentController() == null) {
			return Activator.PLUGIN_ID;
		}
		return getCurrentController().getPluginID();
	}

	public static synchronized String[] getPluginNames() {
		if (sPluginNames == null) {
			final List<String> lil = new ArrayList<>();
			for (final String ep : ExtensionPoints.PLUGIN_EPS) {
				for (final IConfigurationElement elem : Platform.getExtensionRegistry()
						.getConfigurationElementsFor(ep)) {
					final String classname = elem.getAttribute("class");
					lil.add(classname.substring(0, classname.lastIndexOf(".")));
				}
			}
			sPluginNames = lil.toArray(new String[0]);
		}
		return sPluginNames;
	}

	@Override
	public IToolchainData<ToolchainListType> createToolchainData(final String filename)
			throws FileNotFoundException, JAXBException, SAXException {
		if (!new File(filename).exists()) {
			throw new FileNotFoundException("The specified toolchain file " + filename + " was not found");
		}

		final ToolchainStorage tcStorage = new ToolchainStorage();
		return new ToolchainData(filename, tcStorage, tcStorage);
	}

	@Override
	public IToolchainData<ToolchainListType> createToolchainData() {
		final ToolchainStorage tcStorage = new ToolchainStorage();
		return new ToolchainData(tcStorage, tcStorage);
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
		return new CorePreferenceInitializer();
	}

	@Override
	public ILoggingService getCoreLoggingService() {
		return mCoreStorage.getLoggingService();
	}

	@Override
	public IPreferenceProvider getPreferenceProvider(final String pluginId) {
		return mCoreStorage.getPreferenceProvider(pluginId);
	}

	private static final class UltimateJobChangeAdapter extends JobChangeAdapter {
		private final ILogger mLogger;

		private UltimateJobChangeAdapter(final ILogger logger) {
			mLogger = logger;
		}

		@Override
		public void done(final IJobChangeEvent event) {
			if (event == null) {
				return;
			}
			if (event.getResult() == null) {
				return;
			}
			if (event.getResult().getException() == null) {
				return;
			}
			mLogger.error("Error during toolchain job processing:", event.getResult().getException());
		}
	}
}
