/**
 * Servlet implementation class UltimateInterface.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.io.IOException;
import java.io.PrintWriter;

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
		mLogger = new ServletLogger(this, "Servlet", DEBUG);
		System.out.println("##########################");
		System.out.println("## UltimateHttpServlet  ##");
		System.out.println("##########################");
		System.out.println();
		System.out.println("Starting Server ...");
	}

	@Override
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		mLogger.logDebug("Connection from " + request.getRemoteAddr() + ", GET: " + request.getQueryString());
		processRequest(request, response);
	}

	@Override
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException,
			IOException {
		mLogger.logDebug("Connection from " + request.getRemoteAddr() + ", POST: " + request.getQueryString()
				+ " Reading All Request Parameters");
		processRequest(request, response);
	}

	private void processRequest(HttpServletRequest request, HttpServletResponse response) throws IOException {
		ServletLogger sessionLogger = new ServletLogger(this, request.getSession().getId(), DEBUG);
		Request internalRequest = new Request(request, sessionLogger);
		response.setContentType("application/json");
		PrintWriter out = response.getWriter();

		if (internalRequest.containsKey("callback")) {
			out.write(internalRequest.get("callback")[0] + "(");
		}

		writeJSONResponse(internalRequest, out);

		if (internalRequest.containsKey("callback")) {
			out.write(")");
		}
	}

	private void writeJSONResponse(Request request, PrintWriter out) {
		try {
			JSONObject json = new JSONObject();

			if (request.containsKey("example")) {
				Example ex = Example.get(request.get("example")[0]);
				if (ex != null) {
					json.put("exampleContent", ex.getFileContent());
				}
			} else if (request.containsKey("action")) {
				json = handleAction(request);
				json.put("status", "success");
			} else {
				json = new JSONObject();
				json.put("error", "Invalid Request! error code UI01");
				request.getLogger().logDebug("This was an invalid request!");
			}
			json.write(out);
		} catch (JSONException e) {
			String message = "{\"error\" : \"Invalid Request! error code UI02\"}";
			out.print(message);
			request.getLogger().logDebug(message);

			if (DEBUG) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * Handles a request where the "action" parameter is set!
	 * 
	 * @param request
	 *            the parameter list of the request
	 * @return a json object holding the values that should be sent to the
	 *         browser
	 * @throws JSONException
	 *             happens when JSONObject is not used correctly
	 */
	private JSONObject handleAction(Request request) throws JSONException {
		String[] actions = request.get("action");
		if (actions.length != 1) {
			JSONObject json = new JSONObject();
			json.put("error", "Invalid request! error code UI03");
			return json;
		}
		String action = actions[0];
		if (action.equals("execute")) {
			UltimateExecutor executor = new UltimateExecutor(request.getLogger());
			return executor.executeUltimate(request);
		} else {
			JSONObject json = new JSONObject();
			json.put("error", "Invalid request! error code UI05");
			request.getLogger().logDebug("Don't know how to handle action: " + action);
			return json;
		}
	}
}
