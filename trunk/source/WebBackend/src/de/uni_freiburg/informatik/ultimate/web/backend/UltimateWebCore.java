package de.uni_freiburg.informatik.ultimate.web.backend;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import javax.xml.bind.JAXBException;

import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.xml.sax.SAXException;

import com.google.gson.Gson;
import com.google.gson.JsonParseException;
import com.google.gson.reflect.TypeToken;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginFactory;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.SettingsManager;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainManager;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.ApiResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.ErrorResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.GenericResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.ToolchainResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.util.FileUtil;
import de.uni_freiburg.informatik.ultimate.web.backend.util.Request;
import de.uni_freiburg.informatik.ultimate.web.backend.util.WebBackendToolchainJob;

public class UltimateWebCore implements ICore<RunDefinition>, IController<RunDefinition> {

	private static final String ULTIMATE_VERSION = new UltimateCore().getUltimateVersionString();

	private final ILogger mLogger;
	private final ToolchainManager mToolchainManager;
	private final ToolchainStorage mCoreStorage;
	private final SettingsManager mSettingsManager;
	private final PluginFactory mPluginFactory;
	private final ILoggingService mLoggingService;

	private final ConcurrentHashMap<Long, JobMetdata> mJobMetadata;

	public UltimateWebCore() {
		mCoreStorage = new ToolchainStorage();
		mLoggingService = mCoreStorage.getLoggingService();
		mLoggingService.setCurrentControllerID(getPluginID());
		mLogger = mLoggingService.getLogger(UltimateWebCore.class);
		mSettingsManager = new SettingsManager(mLogger);
		mSettingsManager.registerPlugin(this);
		mPluginFactory = new PluginFactory(mSettingsManager, mLogger);
		mToolchainManager = new ToolchainManager(mLoggingService, mPluginFactory, this);
		mJobMetadata = new ConcurrentHashMap<>();
	}

	/**
	 * Initiate ultimate run for the request. Return the results as a json object.
	 *
	 */
	public ApiResponse scheduleUltimateRun(final Request request) {
		try {
			final String action = request.getSingleParameter("action");
			if (!action.equals("execute")) {
				request.getLogger().debug("Don't know how to handle action: %s", action);
				return new ErrorResponse("Invalid request: Unknown `action` parameter ( " + action + ").");
			}
			return scheduleJob(request);
		} catch (final IllegalArgumentException e) {
			return new ErrorResponse("Invalid request: " + e.getMessage());
		} catch (final IOException e) {
			return new ErrorResponse("Internal server error: " + e.getMessage());
		}
	}

	public ApiResponse cancelToolchainJob(final String jobId) {
		for (final Job job : getPendingToolchainJobs()) {
			final WebBackendToolchainJob tcJob = (WebBackendToolchainJob) job;
			if (tcJob.getId().equals(jobId)) {
				tcJob.cancelToolchain();
				return new GenericResponse(String.format("JobId %s canceled", jobId));
			}
		}
		return new ErrorResponse("Unknown JobId");
	}

	private ToolchainResponse scheduleJob(final Request request) throws IOException {

		final String jobId = request.getRequestId();
		final ToolchainResponse tcResponse = new ToolchainResponse(jobId);

		final IToolchain<RunDefinition> toolchain = requestToolchain(new File[] { prepareInputFile(request) });
		mJobMetadata.put(toolchain.getId(), new JobMetdata(request.getRequestId(), toolchain.getId(),
				prepareToolchainFile(request), getUserSettingsFromRequest(request)));

		try {
			final WebBackendToolchainJob job = new WebBackendToolchainJob("WebBackendToolchainJob for request " + jobId,
					this, this, mLogger, toolchain, jobId);
			job.schedule();
		} catch (final Exception t) {
			mLogger.error("Failed to run Ultimate", t);
			tcResponse.setErrorMessage("Failed to run Ultimate: " + t.getMessage());
		}
		try {
			tcResponse.store(mLogger);
		} catch (final IOException ex) {
			mLogger.error("Failed to store toolchain response for " + request.getRequestId(), ex);
		}
		return tcResponse;
	}

	/**
	 * Set the temporary ultimate input file. As set by the web-frontend user in the editor.
	 *
	 * @param internalRequest
	 * @throws IOException
	 */
	private static File prepareInputFile(final Request request) throws IOException {
		final String code = request.getSingleParameter("code");
		final String fileExtension = request.getSingleParameter("code_file_extension");
		return FileUtil.writeTemporaryFile(request.getRequestId() + "_input" + fileExtension, code);
	}

	/**
	 * Set temporary settings file as sent by the web-frontend.
	 *
	 * @param internalRequest
	 * @throws IOException
	 */
	private static File prepareToolchainFile(final Request request) throws IOException {
		final String tcXml = request.getSingleParameter("ultimate_toolchain_xml");
		return FileUtil.writeTemporaryFile(request.getRequestId() + "_toolchain.xml", tcXml);
	}

	/**
	 * Jobs (by family "WebBackendToolchainJob") running or queued.
	 *
	 * @return
	 */
	private static Job[] getPendingToolchainJobs() {
		final IJobManager jobManager = Job.getJobManager();
		return jobManager.find("WebBackendToolchainJob");
	}

	/**
	 * Add user frontend settings to the plugins in the toolchain.
	 *
	 * @param toolchain
	 * @return Updated UltimateServiceProvider
	 */
	public IUltimateServiceProvider addUserSettings(final IToolchain<RunDefinition> toolchain) {
		// TODO: Add timeout to the API request and use it.

		mLogger.info("Apply user settings to run configuration.");
		final List<Map<String, Object>> userSettings = mJobMetadata.get(toolchain.getId()).getUserSettings();
		final IUltimateServiceProvider services = toolchain.getCurrentToolchainData().getServices();
		if (Config.FORCED_TIMEOUT > 0) {
			services.getProgressMonitorService().setDeadline(System.currentTimeMillis() + Config.FORCED_TIMEOUT * 1000);
		}
		if (userSettings.isEmpty()) {
			return services;
		}

		// TODO: DD: Check that this works as intended, in particular under multiple clients.
		final IUltimateServiceProvider newServices =
				services.registerPreferenceLayer(UltimateWebCore.class, getRegisteredUltimatePluginIDs());

		for (final Map<String, Object> userSetting : userSettings) {
			final String pluginId = userSetting.get("plugin_id").toString();
			final String key = userSetting.get("key").toString();

			// Check if the setting is in the white-list.
			if (!Config.USER_SETTINGS_WHITELIST.isPluginKeyWhitelisted(pluginId, key)) {
				mLogger.warn("Setting '%s' for plugin %s is not in whitelist.", key, pluginId);
				continue;
			}

			// Apply the setting.
			switch (userSetting.get("type").toString()) {
			case "bool":
			case "int":
			case "string":
			case "real":
				String valueSource = "value";
				Object value = userSetting.get(valueSource);
				if (value == null) {
					valueSource = "default";
					value = userSetting.get(valueSource);
				}
				if (value == null) {
					mLogger.info("No value for setting %s '%s'", pluginId, key);
				} else {
					newServices.getPreferenceProvider(pluginId).put(key, value);
					mLogger.info("Set %s %s=%s from '%s'", pluginId, key, value, valueSource);
				}
				break;
			default:
				mLogger.info("User setting type %s is unknown. Ignoring", userSetting.get("type"));
				break;
			}
		}

		return newServices;
	}

	/**
	 * Get user settings of the form <code>
	 * {
	        "plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
	        "default": false,
	        "visible": false,
	        "name": "Check if freed pointer was valid",
	        "id": "cacsl2boogietranslator.check.if.freed.pointer.was.valid",
	        "type": "bool",
	        "key": "Check if freed pointer was valid"
	    }
	 * </code> from the request.
	 */
	private List<Map<String, Object>> getUserSettingsFromRequest(final Request request) {
		try {
			final String usParam = request.getSingleParameter("user_settings");
			final Map<String, List<Map<String, Object>>> parsed =
					new Gson().fromJson(usParam, new TypeToken<Map<String, List<Map<String, Object>>>>() {
					}.getType());
			return parsed.get("user_settings");
		} catch (final JsonParseException e) {
			mLogger.error("Could not fetch user settings: %s", e.getMessage());
			return Collections.emptyList();
		}
	}

	@Override
	public IToolchainData<RunDefinition> createToolchainData(final String filename)
			throws FileNotFoundException, JAXBException, SAXException {
		if (!new File(filename).exists()) {
			throw new FileNotFoundException("The specified toolchain file " + filename + " was not found");
		}

		final ToolchainStorage tcStorage = new ToolchainStorage();
		return new ToolchainData(filename, tcStorage, tcStorage);
	}

	@Override
	public IToolchainData<RunDefinition> createToolchainData() {
		final ToolchainStorage tcStorage = new ToolchainStorage();
		return new ToolchainData(tcStorage, tcStorage);
	}

	@Override
	public IToolchain<RunDefinition> requestToolchain(final File[] inputFiles) {
		return mToolchainManager.requestToolchain(inputFiles);
	}

	@Override
	public void releaseToolchain(final IToolchain<RunDefinition> toolchain) {
		mToolchainManager.releaseToolchain(toolchain);
		mJobMetadata.remove(toolchain.getId());
	}

	@Override
	public void savePreferences(final String absolutePath) {
		// not necessary
	}

	@Override
	public void loadPreferences(final String absolutePath, final boolean silent) {
		// not necessary
	}

	@Override
	public void resetPreferences(final boolean silent) {
		// not necessary
	}

	@Override
	public IUltimatePlugin[] getRegisteredUltimatePlugins() {
		final Set<IUltimatePlugin> rtr = new LinkedHashSet<>();
		rtr.add(this);
		rtr.addAll(mPluginFactory.getAllAvailableToolchainPlugins());
		return rtr.toArray(new IUltimatePlugin[rtr.size()]);
	}

	@Override
	public String[] getRegisteredUltimatePluginIDs() {
		final List<String> rtr = mPluginFactory.getPluginIds();
		return rtr.toArray(new String[rtr.size()]);
	}

	@Override
	public ILoggingService getCoreLoggingService() {
		return mLoggingService;
	}

	@Override
	public IPreferenceProvider getPreferenceProvider(final String pluginId) {
		throw new UnsupportedOperationException(
				String.format("%s does not support core preference providers", UltimateWebCore.class));
	}

	@Override
	public String getUltimateVersionString() {
		return ULTIMATE_VERSION;
	}

	/************************* End ICore Implementation *********************/

	/******************* Ultimate Plugin Implementation *****************/

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
		return null;
	}

	/**************** End Ultimate Plugin Implementation *****************/

	/**************** IController Implementation *****************/

	@Override
	public int init(final ICore<RunDefinition> core) {
		assert core == this;
		return 0;
	}

	@Override
	public ISource selectParser(final IToolchain<RunDefinition> toolchain, final Collection<ISource> parser) {
		return null;
	}

	@Override
	public IToolchainData<RunDefinition> selectTools(final IToolchain<RunDefinition> toolchain,
			final List<ITool> tools) {
		try {
			final JobMetdata jobMetadata = mJobMetadata.get(toolchain.getId());
			return createToolchainData(jobMetadata.getToolchainFile().getAbsolutePath());
		} catch (FileNotFoundException | JAXBException | SAXException e) {
			mLogger.error("Exception during tool selection: " + e.getClass().getSimpleName() + ": " + e.getMessage());
			return null;
		}
	}

	@Override
	public List<String> selectModel(final IToolchain<RunDefinition> toolchain, final List<String> modelNames) {
		throw new UnsupportedOperationException(String.format("%s cannot select models", UltimateWebCore.class));
	}

	@Override
	public IToolchainData<RunDefinition> prerun(final IToolchain<RunDefinition> toolchain) {
		final IToolchainData<RunDefinition> tcData = toolchain.getCurrentToolchainData();
		return tcData.replaceServices(addUserSettings(toolchain));
	}

	@Override
	public void displayToolchainResults(final IToolchain<RunDefinition> toolchain,
			final Map<String, List<IResult>> results) {
		// TODO: Do something here
	}

	@Override
	public void displayException(final IToolchain<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		// TODO: Do something here
	}

	/**************** End IController Implementation *****************/

	private static final class JobMetdata {

		private final String mRequestId;
		private final long mToolchainId;
		private final File mToolchainFile;
		private final List<Map<String, Object>> mUserSettings;

		public JobMetdata(final String requestId, final long toolchainId, final File toolchainFile,
				final List<Map<String, Object>> userSettings) {
			mRequestId = requestId;
			mToolchainId = toolchainId;
			mToolchainFile = toolchainFile;
			mUserSettings = userSettings;
		}

		public String getRequestId() {
			return mRequestId;
		}

		public long getToolchainId() {
			return mToolchainId;
		}

		public File getToolchainFile() {
			return mToolchainFile;
		}

		public List<Map<String, Object>> getUserSettings() {
			return mUserSettings;
		}
	}

}
