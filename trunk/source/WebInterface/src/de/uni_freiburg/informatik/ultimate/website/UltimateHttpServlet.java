/**
 * Servlet implementation class UltimateInterface.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.json.JSONException;
import org.json.JSONObject;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class UltimateHttpServlet extends HttpServlet {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = 1L;
	/**
	 * Whether the Servlet should be executed in Debug-Mode or not.
	 */
	private static final boolean DEBUG = !false;

	private final ServletLogger mLogger;

	/**
	 * Constructor.
	 * 
	 * @see HttpServlet#HttpServlet()
	 */
	public UltimateHttpServlet() {
		super();
		mLogger = new ServletLogger(this, DEBUG);
		System.out.println("##########################");
		System.out.println("## UltimateHttpServlet  ##");
		System.out.println("##########################");
		System.out.println();
		System.out.println("Starting Server ...");
	}

	@Override
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		mLogger.logDebug("Connection from " + request.getRemoteAddr() + "This was a get: " + request.getQueryString());
		processRequest(request, response);
	}

	@Override
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException,
			IOException {
		mLogger.logDebug("Connection from " + request.getRemoteAddr() + "This was a post: " + request.getQueryString()
				+ " Reading All Request Parameters");
		processRequest(request, response);
	}

	private void processRequest(HttpServletRequest request, HttpServletResponse response) throws IOException {
		Map<String, String[]> paramList = extractParameter(request);
		response.setContentType("application/json");
		PrintWriter out = response.getWriter();

		if (paramList.containsKey("callback")) {
			out.write(paramList.get("callback")[0] + "(");
		}

		writeJSONResponse(paramList, out);

		if (paramList.containsKey("callback")) {
			out.write(")");
		}
	}

	private Map<String, String[]> extractParameter(HttpServletRequest request) {
		Map<String, String[]> paramList = new HashMap<String, String[]>();
		Enumeration<String> paramNames = request.getParameterNames();
		while (paramNames.hasMoreElements()) {
			String paramName = paramNames.nextElement();
			String[] paramValues = request.getParameterValues(paramName);
			paramList.put(paramName, paramValues);

			if (DEBUG) {
				StringBuilder sb = new StringBuilder();
				sb.append("\t{");
				sb.append(paramName);
				sb.append("} :: {");
				for (String s : paramValues) {
					sb.append(s);
					sb.append("}");
				}
				mLogger.logDebug(sb.toString());
			}
		}
		return paramList;
	}

	private void writeJSONResponse(Map<String, String[]> paramList, PrintWriter out) {
		try {
			JSONObject json = new JSONObject();

			if (paramList.containsKey("example")) {
				Example ex = Example.get(paramList.get("example")[0]);
				if (ex != null) {
					json.put("exampleContent", ex.getFileContent());
				}
			} else if (paramList.containsKey("action")) {
				json = handleAction(paramList);
				json.put("status", "success");
			} else {
				json = new JSONObject();
				json.put("error", "Invalid Request! error code UI01");
				mLogger.logDebug("This was an invalid request!");
			}
			json.write(out);
		} catch (JSONException e) {
			String message = "{\"error\" : \"Invalid Request! error code UI02\"}";
			out.print(message);
			mLogger.logDebug(message);

			if (DEBUG) {
				e.printStackTrace();
			}
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
	private JSONObject handleAction(Map<String, String[]> paramList) throws JSONException {
		String[] actions = paramList.get("action");
		if (actions.length != 1) {
			JSONObject json = new JSONObject();
			json.put("error", "Invalid request! error code UI03");
			return json;
		}
		String action = actions[0];
		if (action.equals("execute")) {
			UltimateExecutor executor = new UltimateExecutor(mLogger);
			return executor.executeUltimate(paramList);
		} else {
			JSONObject json = new JSONObject();
			json.put("error", "Invalid request! error code UI05");
			mLogger.logDebug("Don't know how to handle action: " + action);
			return json;
		}
	}
}
