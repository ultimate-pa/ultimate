package de.uni_freiburg.informatik.ultimate.web.backend;

import java.io.IOException;
import java.util.Optional;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import de.uni_freiburg.informatik.ultimate.web.backend.dto.ApiResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.ErrorResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.ToolchainResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.VersionResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.util.GetApiRequest;
import de.uni_freiburg.informatik.ultimate.web.backend.util.Request;
import de.uni_freiburg.informatik.ultimate.web.backend.util.ServletLogger;

public class UltimateApiServlet extends HttpServlet {

	private static final long serialVersionUID = 1L;
	private static final boolean DEBUG = true;

	private final ServletLogger mServletLogger;
	private final UltimateWebCore mCore;

	/**
	 * Constructor.
	 *
	 * @see HttpServlet#HttpServlet()
	 */
	public UltimateApiServlet() {
		mServletLogger = new ServletLogger(this, DEBUG);
		mCore = new UltimateWebCore();
	}

	/**
	 * Process GET requests
	 */
	@Override
	protected void doGet(final HttpServletRequest request, final HttpServletResponse response) {
		mServletLogger.debug("Connection from %s, GET: %s%s", request.getRemoteAddr(), request.getRequestURL(),
				request.getQueryString() == null ? "" : "?" + request.getQueryString());
		try {
			processAPIGetRequest(request, response);
		} catch (final IOException ex) {
			mServletLogger.error("Exception during GET: ", ex);
		}

	}

	/**
	 * Process POST requests
	 */
	@Override
	protected void doPost(final HttpServletRequest request, final HttpServletResponse response) {
		mServletLogger.debug("Connection from %s, POST: %s", request.getRemoteAddr(), request.getRequestURI());
		final ServletLogger sessionLogger = new ServletLogger(this, DEBUG);
		final Request internalRequest = new Request(request, sessionLogger);
		try {
			processAPIPostRequest(internalRequest, response);
		} catch (final IOException ex) {
			mServletLogger.error("Exception during POST: ", ex);
		}

	}

	private void processAPIGetRequest(final HttpServletRequest request, final HttpServletResponse response)
			throws IOException {
		final GetApiRequest apiRequest = new GetApiRequest(request);

		try {
			switch (apiRequest.getRessourceType()) {
			case VERSION:
				new VersionResponse(mCore.getUltimateVersionString()).write(response);
				break;
			case JOB:
				handleJobGetRequest(apiRequest).write(response);
				break;
			default:
				new ErrorResponse("unknown request").write(response);
				break;
			}
		} catch (final IOException e) {
			new ErrorResponse(e.getMessage()).write(response);
			mServletLogger.error("IOException during response", e);
		}
	}

	private ApiResponse handleJobGetRequest(final GetApiRequest apiRequest) {
		if (apiRequest.getUrlParts().length < 4) {
			return new ErrorResponse("No JobId provided");
		}

		final String jobId = apiRequest.getUrlParts()[3];
		switch (apiRequest.getTaskType()) {
		case GET:
			final Optional<ToolchainResponse> toolchainResponse = ToolchainResponse.load(mServletLogger, jobId);
			if (toolchainResponse.isEmpty()) {
				return new ErrorResponse("Unknown JobId");
			}
			return toolchainResponse.get();
		case DELETE:
			return mCore.cancelToolchainJob(jobId);
		default:
			return new ErrorResponse("Task not supported for ressource " + apiRequest.getRessourceType());
		}
	}

	/**
	 * Handle POST request. Write result to HttpServletResponse via APIResponse.
	 *
	 * @param internalRequest
	 * @param responseWriter
	 */
	private void processAPIPostRequest(final Request internalRequest, final HttpServletResponse response)
			throws IOException {
		try {
			mServletLogger.debug("Process API POST request.");
			if (internalRequest.getParameterList().containsKey("action")) {
				mServletLogger.debug("Initiate Ultimate run for request: %s", internalRequest.toString());
				mCore.scheduleUltimateRun(internalRequest).write(response);
			} else {
				new ErrorResponse("Invalid request: Missing `action` parameter.").write(response);
			}

		} catch (final IOException e) {
			new ErrorResponse(e.getMessage()).write(response);
			mServletLogger.error("IOException during POST", e);
		}
	}

}
