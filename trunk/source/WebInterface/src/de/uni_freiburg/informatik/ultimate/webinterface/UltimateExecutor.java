package de.uni_freiburg.informatik.ultimate.webinterface;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;

import org.json.JSONException;
import org.json.JSONObject;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting.SettingType;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;

public class UltimateExecutor {

	private final ServletLogger mLogger;

	/**
	 * Upper bound for the all timeouts that are set by {@link WebToolchain}s. While executing a toolchain Ultimate uses
	 * the minimum of this number and the timeout of the {@link WebToolchain}. Reducing this to a small number is
	 * helpful if the website is running on a computer that is not able to handle many requests in parallel.
	 */
	private static final long TIMEOUT = 24 * 60 * 60 * 1000;

	public UltimateExecutor(final ServletLogger logger) {
		mLogger = logger;
	}

	public JSONObject executeUltimate(final Request internalRequest) throws JSONException {
		return handleActionExecute(internalRequest);
	}

	private JSONObject handleActionExecute(final Request internalRequest) throws JSONException {
		JSONObject json = new JSONObject();

		File inputFile = null;
		File settingsFile = null;
		File toolchainFile = null;

		try {
			final String taskId = getCheckedArgument(internalRequest, "taskID");
			final String tcId = getCheckedArgument(internalRequest, "tcID");
			final String code = getCheckedArgument(internalRequest, "code");

			mLogger.log("Preparing to execute Ultimate for task ID " + taskId + " and toolchain ID " + tcId + "...");

			final WebToolchain tc = getToolchain(taskId, tcId);
			if (tc == null) {
				throw new IllegalArgumentException(
						"Invalid task or toolchain ID. taskID=" + taskId + ", toolchainID=" + tcId);
			}
			// Apply the current user settings that are contained in the request
			// to the settings instances defined by the toolchain
			applyUserSettings(internalRequest, tcId, tc);

			// create temporary files to run ultimate on
			final String timestamp = CoreUtil.getCurrentDateTimeAsString();
			inputFile = writeTemporaryFile(timestamp + "_input", code, getFileExtension(taskId));
			settingsFile = writeTemporaryFile(timestamp + "_settings", tc.getSettingFileContent(), ".epf");
			toolchainFile = writeTemporaryFile(timestamp + "_toolchain", tc.getToolchainXML(), ".xml");

			// TODO: write additional settings file that will be loaded after
			// the default settings file was loaded Apply additional settings
			mLogger.log("Written temporary files to " + inputFile.getParent() + " with timestamp " + timestamp);

			// run ultimate
			final long timeout = Math.min(tc.getTimeout(), TIMEOUT);
			if (runUltimate(json, inputFile, settingsFile, toolchainFile, timeout)) {
				mLogger.log("Finished executing Ultimate for task ID " + taskId + " and toolchain ID " + tcId + "...");
			} else {
				mLogger.log(
						"Ultimate terminated abnormally for task ID " + taskId + " and toolchain ID " + tcId + "...");
			}

		} catch (final IllegalArgumentException e) {
			json = new JSONObject();
			json.put("error", "Invalid request: Error code UI04.");
			mLogger.log("Internal server error: " + e.getClass().getSimpleName());
			mLogger.logDebug(e.toString());
		} catch (final IOException e) {
			json = new JSONObject();
			json.put("error", "Internal server error: IO");
			mLogger.log("Internal server error: " + e.getClass().getSimpleName());
			mLogger.logDebug(e.toString());
		} catch (final Throwable e) {
			json = new JSONObject();
			json.put("error", "Internal server error: Generic");
			mLogger.log("Internal server error: " + e.getClass().getSimpleName());
			mLogger.logDebug(e.toString());
		} finally {
			postProcessTemporaryFiles(settingsFile, toolchainFile, inputFile);
		}
		if (json.length() < 1) {
			json.put("error", "Internal server error: No message produced");
			mLogger.log("Internal server error: No message produced");
		}
		return json;
	}

	private static String getCheckedArgument(final Request internalRequest, final String paramId) {
		final String[] rtr = internalRequest.getParameterList().get(paramId);

		if (rtr == null) {
			throw new IllegalArgumentException("The parameter \"" + paramId + "\" was not supplied");
		}
		if (rtr.length != 1) {
			throw new IllegalArgumentException("The parameter \"" + paramId
					+ "\" has an unexpected length (Expected 1, but was " + rtr.length + ")");
		}

		return rtr[0];
	}

	private boolean runUltimate(final JSONObject json, final File inputFile, final File settingsFile,
			final File toolchainFile, final long timeout) throws JSONException {
		try {
			mLogger.log("Starting Ultimate...");
			final UltimateWebController uwc =
					new UltimateWebController(mLogger, settingsFile, inputFile, toolchainFile, timeout);
			uwc.runUltimate(json);
		} catch (final Throwable t) {
			mLogger.log("fail");
			final String sep = CoreUtil.getPlatformLineSeparator();
			final String message = "failed to run ULTIMATE" + sep + t.toString() + sep + t.getMessage();
			mLogger.log(message);
			json.put("error", message);
			return false;
		}
		return true;
	}

	private void postProcessTemporaryFiles(final File settingsFile, final File tcFile, final File codeFile) {
		final File logDir = new File(System.getProperty("java.io.tmpdir") + File.separator + "log" + File.separator);
		if (!logDir.exists()) {
			logDir.mkdir();
		}
		mLogger.log("Moving input, setting and toolchain file to " + logDir.getAbsoluteFile());
		if (codeFile != null) {
			codeFile.renameTo(new File(logDir, codeFile.getName()));
		}
		if (settingsFile != null) {
			settingsFile.renameTo(new File(logDir, settingsFile.getName()));
		}
		if (tcFile != null) {
			tcFile.renameTo(new File(logDir, tcFile.getName()));
		}
	}

	private static File writeTemporaryFile(final String name, final String content, final String fileExtension)
			throws IOException {
		final File codeFile = File.createTempFile(name, fileExtension);
		try (final Writer fstream = new OutputStreamWriter(new FileOutputStream(codeFile), StandardCharsets.UTF_8)) {
			fstream.write(content);
		}
		return codeFile;
	}

	private static String getFileExtension(final String taskId) {
		final TaskNames taskName = TaskNames.valueOf(taskId);
		String fileExtension;

		switch (taskName) {
		case AUTOMATA_SCRIPT:
			fileExtension = ".ats";
			break;
		case AUTOMIZER_BOOGIE:
		case CONCURRENT_BOOGIE:
		case RANK_SYNTHESIS_BOOGIE:
		case TERMINATION_BOOGIE:
		case KOJAK_BOOGIE:
		case TAIPAN_BOOGIE:
			fileExtension = ".bpl";
			break;
		case AUTOMIZER_C:
		case LTLAUTOMIZER_C:
		case RANK_SYNTHESIS_C:
		case TERMINATION_C:
		case KOJAK_C:
		case TAIPAN_C:
			fileExtension = ".c";
			break;
		default:
			throw new IllegalArgumentException("The given taskId is unknown to UltimateInterface: " + taskId);
		}
		return fileExtension;
	}

	private static void applyUserSettings(final Request internalRequest, final String toolchainId,
			final WebToolchain toolchain) {
		for (final Setting setting : toolchain.getUserModifiableSettings()) {
			final String sid = toolchainId + "_" + setting.getSettingIdentifier();
			if (!internalRequest.getParameterList().containsKey(sid)) {
				continue;
			}

			if (setting.getType() != SettingType.DROPDOWN && internalRequest.getParameterList().get(sid).length != 1) {
				throw new IllegalArgumentException("Setting ID not unique: " + sid);
			}
			switch (setting.getType()) {
			case BOOLEAN:
				setting.setBooleanValue(internalRequest.getParameterList().get(sid)[0]);
				break;
			case DROPDOWN:
				setting.setDropDownValue(internalRequest.getParameterList().get(sid));
				break;
			case INTEGER:
				setting.setIntValue(internalRequest.getParameterList().get(sid)[0]);
				break;
			case STRING:
				setting.setStringValue(internalRequest.getParameterList().get(sid)[0]);
				break;
			default:
				throw new IllegalArgumentException("Setting type " + setting.getType() + " is unknown");
			}
		}
	}

	private static WebToolchain getToolchain(final String taskId, final String tcId) {
		// get user settings for this toolchain
		final ArrayList<WebToolchain> tcs = Tasks.getActiveToolchains().get(taskId);
		if (tcs == null) {
			return null;
		}
		WebToolchain tc = null;
		for (final WebToolchain currentTC : tcs) {
			if (currentTC.getId().equals(tcId)) {
				tc = currentTC;
				break;
			}
		}
		return tc;
	}

}
