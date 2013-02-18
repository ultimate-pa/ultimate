/**
 * Servlet implementation class UltimateInterface.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import de.uni_freiburg.informatik.ultimate.cloud.IUltimate;
import de.uni_freiburg.informatik.ultimate.cloud.UltimateCloud;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.InvariantResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.website.Setting.SettingType;

/**
 * @author Christoph Hofmann
 * @date 31.07.2012
 */
public class UltimateCloudInterface extends HttpServlet {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor.
	 * 
	 * @see HttpServlet#HttpServlet()
	 */
	public UltimateCloudInterface() {
		super();

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * javax.servlet.http.HttpServlet#doGet(javax.servlet.http.HttpServletRequest
	 * , javax.servlet.http.HttpServletResponse)
	 */
	@Override
	protected void doGet(HttpServletRequest request,
			HttpServletResponse response) throws ServletException, IOException {

		Map<String, String[]> paramList = parseParameters(request);
		PrintWriter out = prepareResponse(response, paramList);

		JSONObject json = new JSONObject();

		try {
			if (paramList.containsKey("example")) {

				Example ex = Example.get(paramList.get("example")[0]);

				if (ex != null) {
					json.put("exampleContent", ex.getFileContent());
				}

			} else if (paramList.containsKey("result")) {
				
				String id = paramList.get("id")[0];
				
				IUltimate ultimate = new UltimateCloud();
				ultimate.getResult(id);
				
			} else {
				json = new JSONObject();
				json.put("error", "Invalid Request!");
			}

			json.write(out);

		} catch (JSONException e) {
			out.print("{\"error\" : \"Internal server error!\"}");
		}

		finishRespond(paramList, out);
	}

	private PrintWriter prepareResponse(HttpServletResponse response,
			Map<String, String[]> paramList) throws IOException {
		response.setContentType("application/json");
		PrintWriter out = response.getWriter();

		if (paramList.containsKey("callback")) {
			out.write(paramList.get("callback")[0] + "(");
		}

		return out;
	}
	
	private void finishRespond(Map<String, String[]> paramList, PrintWriter out) {
		if (paramList.containsKey("callback")) {
			out.write(")");
		}
	}

	private Map<String, String[]> parseParameters(HttpServletRequest request) {

		Map<String, String[]> paramList = new HashMap<String, String[]>();
		@SuppressWarnings("unchecked")
		Enumeration<String> paramNames = request.getParameterNames();

		while (paramNames.hasMoreElements()) {
			String paramName = paramNames.nextElement();
			String[] paramValues = request.getParameterValues(paramName);
			paramList.put(paramName, paramValues);
		}
		return paramList;

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * javax.servlet.http.HttpServlet#doPost(javax.servlet.http.HttpServletRequest
	 * , javax.servlet.http.HttpServletResponse)
	 */
	@Override
	protected void doPost(HttpServletRequest request,
			HttpServletResponse response) throws ServletException, IOException {

		Map<String, String[]> paramList = parseParameters(request);
		PrintWriter out = prepareResponse(response, paramList);

		try {
			JSONObject json;
			if (paramList.containsKey("action")) {
				json = handleAction(paramList);
				json.put("status", "success");
			} else {
				// if nothing else applies
				json = new JSONObject();
				json.put("error", "Invalid Request!");
			}

			json.write(out);
		} catch (JSONException e) {

			out.print("{\"error\" : \"Invalid Request!\"}");

		}

		finishRespond(paramList, out);
	}

	/**
	 * Handles a request where the "action" parameter is set!
	 * 
	 * @param paramList
	 *            the parameter list of the request
	 * @return a json object holding the values that should be sent to the
	 *         browser
	 * @throws JSONException
	 *             happens when JSONObject is not used correctly
	 */
	private static JSONObject handleAction(Map<String, String[]> paramList)
			throws JSONException {

		JSONObject json = new JSONObject();
		String[] actions = paramList.get("action");

		if (actions.length != 1) {
			json.put("error", "Invalid request!");
			return json;
		}

		File codeFile = null;
		File settingsFile = null;
		File tcFile = null;
		String action = actions[0];

		if (action.equals("execute")) {
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

				Toolchain toolchain = createToolchain(taskId, tcId);
				
				if (toolchain == null) {
					throw new IllegalArgumentException("Invalid toolchain id: " + tcId);
				}
		
				String settingsFileString = toolchain.getSettingFile();
				
				// Build the setting ids to be requested
				// and put the values into the settings object
				String settingPrefix = "sel_tc_" + tcId + "_";
				for (Tool t : toolchain.getTools()) {
					for (Setting s : t.getUserChangeableSettings()) {
						String sid = settingPrefix + t.getHTMLId() + "_"
								+ s.getSettingIdentifier();
						if (paramList.containsKey(sid)) {
							
							if (s.getType() != SettingType.DROPDOWN && paramList.get(sid).length != 1) {
								throw new IllegalArgumentException("Setting ID not unique: " + sid);
							}
							
							switch (s.getType()) {
							case BOOLEAN:
								if (!paramList.get(sid)[0].equals(s.getSettingIdentifier())) {
									throw new IllegalArgumentException("The checkbox value '"+ paramList.get(sid)
											+ "' is unexpected for "+ sid);
								}

								// contained in param list means true
								s.setBooleanValue("true");
								break;
							case DROPDOWN:
								s.setDropDownValue(paramList.get(sid));
								break;
							case INTEGER:
								s.setIntValue(paramList.get(sid)[0]);
								break;
							case STRING:
								s.setStringValue(paramList.get(sid)[0]);
								break;
							default:

							}
						} else {
							if (s.getType().equals(SettingType.BOOLEAN)) {
								s.setBooleanValue("false");
							}
						}
						// else default value will be used (i.e. for
						// mandatory settings)
					}
				}
				
				String fileExtension;

				if (taskId.equals("VerifyC")) {
					fileExtension = "c";
				} else if (taskId.equals("VerifyBoogie")) {
					fileExtension = ".bpl";
				} else if (taskId.equals("RunAutomataTestFile")) {
					fileExtension = ".fat";
				} else if (taskId.equals("RunSmt2Script")) {
					fileExtension = ".smt";
				} else {
					throw new IllegalArgumentException("The given taskId is unknown to UltimateInterface: " + taskId);
				}
				
				//create Id for verification task
				UUID taskName = UUID.randomUUID();	
				
				//start verfication
				IUltimate ultimate = new UltimateCloud();
				ultimate.startUltimate(taskName.toString(), settingsFileString, toolchain, code);
				
				
				// Create temporary file for the code.
				codeFile = File.createTempFile("codeFile", fileExtension);
				BufferedWriter out = new BufferedWriter(new FileWriter(codeFile));
				out.write(code);
				out.close();
				//app.setM_InputFile(codeFile);

				// Create temporary file for settings.
				settingsFile = File.createTempFile("settingsFile", ".epf");
				out = new BufferedWriter(new FileWriter(settingsFile));
				out.write(toolchain.getSettingFile());
				out.close();
				//app.setSettingsFile(settingsFile);

				// Create temporary file for the toolchain.
				tcFile = File.createTempFile("tcFile", ".xml");
				out = new BufferedWriter(new FileWriter(tcFile));
				out.write(toolchain.getToolchainXML());
				out.close();
				//app.setToolchainXML(tcFile);
		
				json.put("taskId", taskName.toString());
	
			} catch (IllegalArgumentException e) {
				json.put("error", "Invalid request!");

			} catch (IOException e) {
				json.put("error", "Internal server error!");

			} finally {
				
			}

			return json;
		}

		json.put("error", "Invalid request!");
		return json;
	}

	private static void ultimateResulsToJson(JSONObject json, HashMap<String, List<IResult>> results) throws JSONException {
		ArrayList<JSONObject> resultList = new ArrayList<JSONObject>();
		
		for (List<IResult> rList : results.values()) {
			for (IResult r : rList) {
				
				String type = "UNDEF";
				UltimateResult packagedResult = new UltimateResult();
				
				if (r instanceof CounterExampleResult) {
					type = "counter";
					packagedResult.logLvl = "error";
				} else if (r instanceof InvariantResult) {
					type = "invariant";
					packagedResult.logLvl = "info";
				} else if (r instanceof PositiveResult) {
					type = "positive";
					packagedResult.logLvl = "info";
				} else if (r instanceof UnprovableResult) {
					type = "unprovable";
					packagedResult.logLvl = "warning";
				} else if (r instanceof SyntaxErrorResult) {
					type = "syntaxError";
					packagedResult.logLvl = "error";
				} else if (r instanceof TimeoutResult) {
					type = "timeout";
					packagedResult.logLvl = "error";
				} // TODO : Add new "Out of resource" result here ...
				
				ILocation loc = r.getLocation();
				
				packagedResult.shortDesc = r.getShortDescription();
				packagedResult.longDesc = r.getLongDescription();
				packagedResult.startLNr = loc.getStartLine();
				packagedResult.endLNr = loc.getEndLine();
				packagedResult.startCol = loc.getStartColumn();
				packagedResult.endCol = loc.getEndColumn();
				packagedResult.type = type;
				resultList.add(new JSONObject(packagedResult));
			}

			json.put("results", new JSONArray(resultList.toArray(new JSONObject[0])));
		}
	}

	private static Toolchain createToolchain(String taskId, String tcId) {
		
		// get user settings for this toolchain
		ArrayList<Toolchain> tcs = Tasks.getActiveToolchains().get(taskId);
		Toolchain tc = null;
		
		for (Toolchain currentTC : tcs) {
			if (currentTC.getId().equals(tcId)) {
				tc = currentTC;
				break;
			}
		}
		
		return tc;
	}
}
