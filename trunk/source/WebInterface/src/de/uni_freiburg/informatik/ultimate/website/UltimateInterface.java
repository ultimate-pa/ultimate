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

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Application;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Application.Ultimate_Mode;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult.Severity;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.InvariantResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.PossibleUnsoundnessWarningResult;
import de.uni_freiburg.informatik.ultimate.result.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.result.RankingFunctionResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.website.Setting.SettingType;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.12.2011
 */
public class UltimateInterface extends HttpServlet {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = 1L;
	/**
	 * Whether the Servlet should be executed in Debug-Mode or not.
	 */
	private static final boolean DBG = false;

	/**
	 * Constructor.
	 * 
	 * @see HttpServlet#HttpServlet()
	 */
	public UltimateInterface() {
		super();
		if (DBG) {
			System.out.println("########################################");
			System.out.println("## Web-Server interface for Ultimate  ##");
			System.out.println("########################################");
			System.out.println();
			System.out.println("\tOleksii Saukh");
			System.out.println("\tStefan Wissert");
			System.out.println("\tMarkus Lindenmann");
			System.out.println();
			System.out.println("########################################");
			System.out.println();
			System.out.println("Starting Server ...");
		}
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
		if (DBG) {
			System.out.println("Connection from " + request.getRemoteAddr());
			System.out.println("This was a get: " + request.getQueryString());
		}

		Map<String, String[]> paramList = new HashMap<String, String[]>();
		@SuppressWarnings("unchecked")
        Enumeration<String> paramNames = request.getParameterNames();
		while (paramNames.hasMoreElements()) {
			String paramName = paramNames.nextElement();
			String[] paramValues = request.getParameterValues(paramName);
			paramList.put(paramName, paramValues);
		}
		response.setContentType("application/json");
		PrintWriter out = response.getWriter();
		if (paramList.containsKey("callback")) {
			out.write(paramList.get("callback")[0] + "(");
		}
		try {
			JSONObject json = new JSONObject();
			if (paramList.containsKey("example")) {
				Example ex = Example.get(paramList.get("example")[0]);
				if (ex != null) {
					json.put("exampleContent", ex.getFileContent());
				}
			} else {
				json = new JSONObject();
				json.put("error", "Invalid Request! error code UI01");
				if (DBG) {
					System.out.println("This was an invalid request!");
				}
			}
			json.write(out);
		} catch (JSONException e) {
			out.print("{\"error\" : \"Internal server error!\"}");
			if (DBG) {
				e.printStackTrace();
			}
		}
		if (paramList.containsKey("callback")) {
			out.write(")");
		}
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
		response.setContentType("application/json");
		PrintWriter out = response.getWriter();

		if (DBG) {
			System.out.println("Connection from " + request.getRemoteAddr());
			System.out.println("This was a post: " + request.getQueryString());
			System.out.println("Reading All Request Parameters");
		}
		Map<String, String[]> paramList = new HashMap<String, String[]>();
		@SuppressWarnings("unchecked")
        Enumeration<String> paramNames = request.getParameterNames();
		while (paramNames.hasMoreElements()) {
			String paramName = paramNames.nextElement();
			String[] paramValues = request.getParameterValues(paramName);
			paramList.put(paramName, paramValues);
			if (DBG) {
				System.out.print("\t{" + paramName + "} :: {");
				for (String s : paramValues) {
					System.out.print(s + "}");
				}
				System.out.println();
			}
		}

		if (paramList.containsKey("callback")) {
			out.write(paramList.get("callback")[0] + "(");
		}

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
			out.print("{\"error\" : \"Invalid Request! error code UI02\"}");
			if (DBG) {
				e.printStackTrace();
			}
		}
		if (paramList.containsKey("callback")) {
			out.write(")");
		}
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
			json.put("error", "Invalid request! error code UI03");
			return json;
		}
		File codeFile = null;
		File settingsFile = null;
		File tcFile = null;
		boolean toBeLogged = !false;
		String action = actions[0];
		if (action.equals("execute")) {
			try {
				String[] taskIDs = paramList.get("taskID");
				String[] tcIDs = paramList.get("tcID");
				String[] codes = paramList.get("code");
				if (taskIDs.length != 1 || tcIDs.length != 1
						|| codes.length != 1) {
					throw new IllegalArgumentException("Illegal arguments!");
				}
				String taskId = taskIDs[0];
				String tcId = tcIDs[0];
				String code = codes[0];
				if (DBG) {
					System.out.println("Execute ultimate for: " + taskId + ", "
							+ tcId);
				}
				// get user settings for this toolchain
				ArrayList<Toolchain> tcs = Tasks.getActiveToolchains().get(
						taskId);
				Toolchain tc = null;
				for (Toolchain currentTC : tcs) {
					if (currentTC.getId().equals(tcId)) {
						tc = currentTC;
						break;
					}
				}
				if (tc == null) {
					throw new IllegalArgumentException("Invalid toolchain id: "
							+ tcId);
				}
				// Build the setting ids to be requested
				// and put the values into the settings object
				String settingPrefix = "sel_tc_" + tcId + "_";
				for (Tool t : tc.getTools()) {
					for (Setting s : t.getUserChangeableSettings()) {
						String sid = settingPrefix + t.getHTMLId() + "_"
								+ s.getSettingIdentifier();
						if (paramList.containsKey(sid)) {
							if (s.getType() != SettingType.DROPDOWN
									&& paramList.get(sid).length != 1) {
								throw new IllegalArgumentException(
										"Setting ID not unique: " + sid);
							}
							switch (s.getType()) {
							case BOOLEAN:
								if (!paramList.get(sid)[0].equals(s
										.getSettingIdentifier())) {
									throw new IllegalArgumentException(
											"The checkbox value '"
													+ paramList.get(sid)
													+ "' is unexpected for "
													+ sid);
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
				// execute ultimate with the calculated toolchain settings
				Application app = new Application(
						Ultimate_Mode.EXTERNAL_EXECUTION);
				String fileExtension;
				if (taskId.equals("VerifyC")) {
					fileExtension = "c";
				} else if (taskId.equals("VerifyBoogie")) {
					fileExtension = ".bpl";
				} else if (taskId.equals("RunAutomataTestFile")) {
					fileExtension = ".fat";
				} else if (taskId.equals("RunSmt2Script")) {
					fileExtension = ".smt";
				} else if (taskId.equals("TERMINATION_C")) {
					fileExtension = ".c";
				} else if (taskId.equals("TERMINATION_BOOGIE")) {
					fileExtension = ".bpl";
				} else {
					throw new IllegalArgumentException(
							"The given taskId is unknown to UltimateInterface: "
									+ taskId);
				}
				// Create temporary file for the code.
				codeFile = File.createTempFile("codeFile", fileExtension);
				BufferedWriter out = new BufferedWriter(
						new FileWriter(codeFile));
				out.write(code);
				out.close();
				app.setM_InputFile(codeFile);
				// Create temporary file for settings.
				settingsFile = File.createTempFile("settingsFile", ".epf");
				out = new BufferedWriter(new FileWriter(settingsFile));
				out.write(tc.getSettingFile());
				out.close();
				app.setSettingsFile(settingsFile);
				// Create temporary file for the toolchain.
				tcFile = File.createTempFile("tcFile", ".xml");
				out = new BufferedWriter(new FileWriter(tcFile));
				out.write(tc.getToolchainXML());
				out.close();
				app.setToolchainXML(tcFile);
				try {
					Thread t = new Thread();
					app.start(null);
				} catch (Throwable t) {
					toBeLogged = true;
				}
				// get Result from Ultimate
				UltimateServices us = UltimateServices.getInstance();
				HashMap<String, List<IResult>> results = us.getResultMap();
				// add result to the json object
				ArrayList<JSONObject> resultList = new ArrayList<JSONObject>();
				for (List<IResult> rList : results.values()) {
					for (IResult r : rList) {
						String type = "UNDEF";
						UltimateResult packagedResult = new UltimateResult();
						if (r instanceof CounterExampleResult) {
							type = "counter";
							packagedResult.logLvl = "error";
						} else if (r instanceof ProcedureContractResult) {
							type = "invariant";
							packagedResult.logLvl = "info";
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
//						} else if (r instanceof PossibleUnsoundnessWarningResult<?>) {
//							type = "warning";
//							packagedResult.logLvl = "warning";
						} else if (r instanceof GenericResult<?>) {
							GenericResult<?> rGen = (GenericResult<?>) r;
							if (rGen.getSeverity().equals(Severity.ERROR)) {
								type = "error";
								packagedResult.logLvl = "error";
							} else if (rGen.getSeverity().equals(Severity.WARNING)) {
								type = "warning";
								packagedResult.logLvl = "warning";
							} else if (rGen.getSeverity().equals(Severity.INFO)) {
								type = "info";
								packagedResult.logLvl = "info";
							} else {
								throw new IllegalArgumentException("Unknown kind of severity.");
							}
						} else if (r instanceof NoResult<?>) {
							type = "noResult";
							packagedResult.logLvl = "warning";
						}
						// TODO : Add new "Out of resource" result here ...
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
			} catch (IllegalArgumentException e) {
				toBeLogged = true;
				json = new JSONObject();
				json.put("error", "Invalid request! error code UI04");
				if (DBG) {
					System.out.println("This was an invalid request! "
							+ e.getMessage());
				}
			} catch (IOException e) {
				json = new JSONObject();
				json.put("error", "Internal server error!");
				if (DBG) {
					System.out.println("There was an unexpected Exception!"
							+ e.getMessage());
					e.printStackTrace();
				}
			} finally {
				if (!toBeLogged) {
					if (codeFile != null) codeFile.delete();
					if (settingsFile != null) settingsFile.delete();
					if (tcFile != null) tcFile.delete();
				} else {
					File logDir = new File(System.getProperty("java.io.tmpdir")+"/log/");
					
					System.out.println("Writing something to " + logDir.getAbsoluteFile());
					if (codeFile != null) codeFile.renameTo(new File(logDir, codeFile.getName()));
					if (settingsFile != null) settingsFile.renameTo(new File(logDir, settingsFile.getName()));
					if (tcFile != null) tcFile.renameTo(new File(logDir, tcFile.getName()));
				}
			}
			if (json.length() < 1) {
				json.put("error", "Unexpected behaviour");
			}
			return json;
		}
		json.put("error", "Invalid request! error code UI05");
		if (DBG) {
			System.out.println("Don't know how to handle action: " + action);
		}
		return json;
	}
}
