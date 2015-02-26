package de.uni_freiburg.informatik.ultimate.website;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import org.json.JSONException;
import org.json.JSONObject;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.website.Setting.SettingType;

public class UltimateExecutor {

	private final ServletLogger mLogger;

	public UltimateExecutor(ServletLogger logger) {
		mLogger = logger;
	}

	public JSONObject executeUltimate(Request internalRequest) throws JSONException {
		return handleActionExecute(internalRequest);
	}

	private JSONObject handleActionExecute(Request internalRequest) throws JSONException {
		JSONObject json = new JSONObject();

		File inputFile = null;
		File settingsFile = null;
		File toolchainFile = null;

		try {
			String taskId = getCheckedArgument(internalRequest, "taskID");
			String tcId = getCheckedArgument(internalRequest, "tcID");
			String code = getCheckedArgument(internalRequest, "code");

			mLogger.log("Preparing to execute Ultimate for task ID " + taskId + " and toolchain ID " + tcId + "...");

			WebToolchain tc = getToolchain(taskId, tcId);
			if (tc == null) {
				throw new IllegalArgumentException("Invalid task or toolchain ID. taskID=" + taskId + ", toolchainID="
						+ tcId);
			}
			// Build the setting ids to be requested
			// and put the values into the settings object
			setUserSettings(internalRequest, tcId, tc);

			// create temporary files to run ultimate on
			String timestamp = CoreUtil.getCurrentDateTimeAsString();
			inputFile = writeTemporaryFile(timestamp + "_input", code, getFileExtension(taskId));
			settingsFile = writeTemporaryFile(timestamp + "_settings", tc.getSettingFileContent(), ".epf");
			toolchainFile = writeTemporaryFile(timestamp + "_toolchain", tc.getToolchainXML(), ".xml");

			mLogger.log("Written temporary files to " + inputFile.getParent() + " with timestamp " + timestamp);

			// run ultimate
			runUltimate(json, inputFile, settingsFile, toolchainFile);
			mLogger.log("Finished executing Ultimate for task ID " + taskId + " and toolchain ID " + tcId + "...");

		} catch (IllegalArgumentException e) {
			e.printStackTrace();
			json = new JSONObject();
			json.put("error", "Invalid request! error code UI04");
			mLogger.logDebug("This was an invalid request! " + e.getMessage());
		} catch (IOException e) {
			e.printStackTrace();
			json = new JSONObject();
			json.put("error", "Internal server error (IO)!");
			mLogger.logDebug("There was an IO Exception:" + e.getMessage());
		} catch (Exception e) {
			mLogger.logDebug("There was an Exception: " + e.getClass().getSimpleName());
			mLogger.logDebug(e.toString());
			json.put("error", "Internal server error (Generic)!");
		} finally {
			postProcessTemporaryFiles(settingsFile, toolchainFile, inputFile);
		}
		if (json.length() < 1) {
			json.put("error", "Internal server error (Unexpected behaviour)!");
		}
		return json;
	}

	private String getCheckedArgument(Request internalRequest, String paramId) {
		String[] rtr = internalRequest.get(paramId);

		if (rtr == null) {
			throw new IllegalArgumentException("The parameter \"" + paramId + "\" was not supplied");
		}
		if (rtr.length != 1) {
			throw new IllegalArgumentException("The parameter \"" + paramId
					+ "\" has an unexpected length (Expected 1, but was " + rtr.length + ")");
		}

		return rtr[0];
	}

	/**
	 * 
	 * @param json
	 * @param toolchainFile
	 * @param settingsFile
	 * @param inputFile
	 * @return true iff ultimate terminated normally, false otherwise
	 * @throws JSONException
	 */
	private boolean runUltimate(JSONObject json, File inputFile, File settingsFile, File toolchainFile)
			throws JSONException {
		try {
			mLogger.logDebug("ULTIMATE Application started");
			UltimateWebController uwc = new UltimateWebController(settingsFile, inputFile, toolchainFile);
			uwc.runUltimate(json);
		} catch (Throwable t) {
			t.printStackTrace();
			final String message = "failed to run ULTIMATE" + System.getProperty("line.separator") + t.toString()
					+ System.getProperty("line.separator") + t.getMessage();
			mLogger.logDebug(message);
			json.put("error", message);
			return false;
		}
		return true;
	}

	private void postProcessTemporaryFiles(File settingsFile, File tcFile, File codeFile) {
		// if (logRun) {
		File logDir = new File(System.getProperty("java.io.tmpdir") + File.separator + "log" + File.separator);
		if (!logDir.exists()) {
			logDir.mkdir();
		}
		System.out.println("Moving input, setting and toolchain file to " + logDir.getAbsoluteFile());
		if (codeFile != null)
			codeFile.renameTo(new File(logDir, codeFile.getName()));
		if (settingsFile != null)
			settingsFile.renameTo(new File(logDir, settingsFile.getName()));
		if (tcFile != null)
			tcFile.renameTo(new File(logDir, tcFile.getName()));
		// } else {
		// if (codeFile != null)
		// codeFile.delete();
		// if (settingsFile != null)
		// settingsFile.delete();
		// if (tcFile != null)
		// tcFile.delete();
		// }
	}

	private File writeTemporaryFile(String name, String content, String fileExtension) throws IOException {
		File codeFile = File.createTempFile(name, fileExtension);
		BufferedWriter out = new BufferedWriter(new FileWriter(codeFile));
		out.write(content);
		out.close();
		return codeFile;
	}

	private String getFileExtension(String taskId) {
		String fileExtension;
		if (taskId.equals("VerifyC")) {
			fileExtension = ".c";
		} else if (taskId.equals("VerifyBoogie")) {
			fileExtension = ".bpl";
		} else if (taskId.equals("AUTOMATA_SCRIPT")) {
			fileExtension = ".ats";
		} else if (taskId.equals("RunSmt2Script")) {
			fileExtension = ".smt";
		} else if (taskId.equals("TERMINATION_C")) {
			fileExtension = ".c";
		} else if (taskId.equals("TERMINATION_BOOGIE")) {
			fileExtension = ".bpl";
		} else if (taskId.equals("RANK_SYNTHESIS_C")) {
			fileExtension = ".c";
		} else if (taskId.equals("RANK_SYNTHESIS_BOOGIE")) {
			fileExtension = ".bpl";
		} else if (taskId.equals("VerifyConcurrentBoogie")) {
			fileExtension = ".bpl";
		} else {
			throw new IllegalArgumentException("The given taskId is unknown to UltimateInterface: " + taskId);
		}
		return fileExtension;
	}

	private void setUserSettings(Request internalRequest, String toolchainId, WebToolchain toolchain) {
		for (Tool tool : toolchain.getTools()) {
			for (Setting setting : tool.getUserChangeableSettings()) {
				String sid = toolchainId + "_" + setting.getSettingIdentifier();
				if (!internalRequest.containsKey(sid)) {
					continue;
				}

				if (setting.getType() != SettingType.DROPDOWN && internalRequest.get(sid).length != 1) {
					throw new IllegalArgumentException("Setting ID not unique: " + sid);
				}
				switch (setting.getType()) {
				case BOOLEAN:
					setting.setBooleanValue(internalRequest.get(sid)[0]);
					break;
				case DROPDOWN:
					setting.setDropDownValue(internalRequest.get(sid));
					break;
				case INTEGER:
					setting.setIntValue(internalRequest.get(sid)[0]);
					break;
				case STRING:
					setting.setStringValue(internalRequest.get(sid)[0]);
					break;
				default:
					throw new IllegalArgumentException("Setting type " + setting.getType() + " is unknown");
				}
			}
		}
	}

	private WebToolchain getToolchain(String taskId, String tcId) {
		// get user settings for this toolchain
		ArrayList<WebToolchain> tcs = Tasks.getActiveToolchains().get(taskId);
		if (tcs == null) {
			return null;
		}
		WebToolchain tc = null;
		for (WebToolchain currentTC : tcs) {
			if (currentTC.getId().equals(tcId)) {
				tc = currentTC;
				break;
			}
		}
		return tc;
	}

}
