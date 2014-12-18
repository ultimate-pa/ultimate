package de.uni_freiburg.informatik.ultimate.website;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Map;

import org.json.JSONException;
import org.json.JSONObject;

import de.uni_freiburg.informatik.ultimate.website.Setting.SettingType;

public class UltimateExecutor {

	private final ServletLogger mLogger;

	public UltimateExecutor(ServletLogger logger) {
		mLogger = logger;
	}

	public JSONObject executeUltimate(Map<String, String[]> requestParams) throws JSONException {
		return handleActionExecute(requestParams);
	}

	private JSONObject handleActionExecute(Map<String, String[]> paramList) throws JSONException {
		JSONObject json = new JSONObject();

		File inputFile = null;
		File settingsFile = null;
		File toolchainFile = null;

		try {
			String[] taskIDs = paramList.get("taskID");
			String[] tcIDs = paramList.get("tcID");
			String[] codes = paramList.get("code");
			if (taskIDs.length != 1 || tcIDs.length != 1 || codes.length != 1) {
				throw new IllegalArgumentException("Illegal arguments!");
			}
			String taskId = taskIDs[0];
			String tcId = tcIDs[0];
			String code = codes[0];
			mLogger.logDebug("Execute ultimate for: " + taskId + ", " + tcId);

			WebToolchain tc = getToolchain(taskId, tcId);
			if (tc == null) {
				throw new IllegalArgumentException("Invalid toolchain id: " + tcId);
			}
			// Build the setting ids to be requested
			// and put the values into the settings object
			setUserSettings(paramList, tcId, tc);

			// create temporary files to run ultimate on
			//TODO: Ensure that the triple settings, input, toolchain has the same ID 
			inputFile = writeTemporaryFile("codeFile", code, getFileExtension(taskId));
			settingsFile = writeTemporaryFile("settingsFile", tc.getSettingFileContent(), ".epf");
			toolchainFile = writeTemporaryFile("tcFile", tc.getToolchainXML(), ".xml");
			runUltimate(json, inputFile, settingsFile, toolchainFile);

		} catch (IllegalArgumentException e) {
			e.printStackTrace();
			json = new JSONObject();
			json.put("error", "Invalid request! error code UI04");
			mLogger.logDebug("This was an invalid request! " + e.getMessage());
		} catch (IOException e) {
			e.printStackTrace();
			json = new JSONObject();
			json.put("error", "Internal server error (IO)!");
			mLogger.logDebug("There was an unexpected Exception!" + e.getMessage());
		} catch (Exception e) {
			mLogger.logDebug("failed construct ULTIMATE run, run ULTIMATE, and present results"
					+ System.getProperty("line.separator") + e.toString() + System.getProperty("line.separator")
					+ e.getMessage());
			json.put("error", "Internal server error (Generic)!");
		} finally {
			postProcessTemporaryFiles(settingsFile, toolchainFile, inputFile);
		}
		if (json.length() < 1) {
			json.put("error", "Internal server error (Unexpected behaviour)!");
		}
		return json;
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
		//TODO: Ensure that the triple settings, input, toolchain has the same ID 
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

	private void setUserSettings(Map<String, String[]> paramList, String tcId, WebToolchain tc) {
		String settingPrefix = "sel_tc_" + tcId + "_";
		for (Tool tool : tc.getTools()) {
			for (Setting setting : tool.getUserChangeableSettings()) {
				String sid = settingPrefix + tool.getHTMLId() + "_" + setting.getSettingIdentifier();
				if (paramList.containsKey(sid)) {
					if (setting.getType() != SettingType.DROPDOWN && paramList.get(sid).length != 1) {
						throw new IllegalArgumentException("Setting ID not unique: " + sid);
					}
					switch (setting.getType()) {
					case BOOLEAN:
						if (!paramList.get(sid)[0].equals(setting.getSettingIdentifier())) {
							throw new IllegalArgumentException("The checkbox value '" + paramList.get(sid)
									+ "' is unexpected for " + sid);
						}
						// contained in param list means true
						setting.setBooleanValue("true");
						break;
					case DROPDOWN:
						setting.setDropDownValue(paramList.get(sid));
						break;
					case INTEGER:
						setting.setIntValue(paramList.get(sid)[0]);
						break;
					case STRING:
						setting.setStringValue(paramList.get(sid)[0]);
						break;
					default:

					}
				} else {
					if (setting.getType().equals(SettingType.BOOLEAN)) {
						setting.setBooleanValue("false");
					}
				}
				// else default value will be used (i.e. for
				// mandatory settings)
			}
		}
	}

	private WebToolchain getToolchain(String taskId, String tcId) {
		// get user settings for this toolchain
		ArrayList<WebToolchain> tcs = Tasks.getActiveToolchains().get(taskId);
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
