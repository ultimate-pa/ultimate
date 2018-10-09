/**
 * Servlet implementation class UltimateInterface.
 */
package de.uni_freiburg.informatik.ultimate.webinterface;

import java.io.IOException;
import java.io.PrintWriter;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.json.JSONException;
import org.json.JSONObject;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Example;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class UltimateHttpServlet extends HttpServlet {
	private static final String CALLBACK = "callback";
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
		// mLogger.log("##########################");
		// mLogger.log("## UltimateHttpServlet ##");
		// mLogger.log("##########################");
		// mLogger.log("");
		// mLogger.log("Starting Server ...");
	}

	@Override
	protected void doGet(final HttpServletRequest request, final HttpServletResponse response)
			throws ServletException, IOException {
		mLogger.logDebug("Connection from " + request.getRemoteAddr() + ", GET: " + request.getQueryString());
		processRequest(request, response);
	}

	@Override
	protected void doPost(final HttpServletRequest request, final HttpServletResponse response)
			throws ServletException, IOException {
		mLogger.logDebug("Connection from " + request.getRemoteAddr() + ", POST: " + request.getQueryString()
				+ " Reading All Request Parameters");
		processRequest(request, response);
	}

	private void processRequest(final HttpServletRequest request, final HttpServletResponse response)
			throws IOException {
		final ServletLogger sessionLogger = new ServletLogger(this, request.getSession().getId(), DEBUG);
		final Request internalRequest = new Request(request, sessionLogger);
		response.setContentType("application/json");
		response.setCharacterEncoding("UTF-8");
		final PrintWriter out = response.getWriter();

		if (internalRequest.getParameterList().containsKey(CALLBACK)) {
			out.write(internalRequest.getParameterList().get(CALLBACK)[0] + "(");
		}

		writeJSONResponse(internalRequest, out);

		if (internalRequest.getParameterList().containsKey(CALLBACK)) {
			out.write(")");
		}
	}

	private static void writeJSONResponse(final Request request, final PrintWriter out) {
		try {
			JSONObject json = new JSONObject();

			if (request.getParameterList().containsKey("example")) {
				final Example ex = Example.get(request.getParameterList().get("example")[0]);
				if (ex != null) {
					json.put("exampleContent", ex.getFileContent());
				}
			} else if (request.getParameterList().containsKey("action")) {
				json = handleAction(request);
				json.put("status", "success");
			} else {
				json = new JSONObject();
				json.put("error", "Invalid Request! error code UI01");
				request.getLogger().logDebug("This was an invalid request!");
			}
			json.write(out);
		} catch (final JSONException e) {
			final String message = "{\"error\" : \"Invalid Request! error code UI02\"}";
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
	 * @return a json object holding the values that should be sent to the browser
	 * @throws JSONException
	 *             happens when JSONObject is not used correctly
	 */
	private static JSONObject handleAction(final Request request) throws JSONException {
		final String[] actions = request.getParameterList().get("action");
		if (actions.length != 1) {
			final JSONObject json = new JSONObject();
			json.put("error", "Invalid request! error code UI03");
			return json;
		}
		final String action = actions[0];
		if (action.equals("execute")) {
			final UltimateExecutor executor = new UltimateExecutor(request.getLogger());
			return executor.executeUltimate(request);
		}
		final JSONObject json = new JSONObject();
		json.put("error", "Invalid request! error code UI05");
		request.getLogger().logDebug("Don't know how to handle action: " + action);
		return json;
	}
}
