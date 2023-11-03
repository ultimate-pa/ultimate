package de.uni_freiburg.informatik.ultimate.web.backend.util;

import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpSession;

public class Request {
	private final Map<String, String[]> mParameterList;
	private final ServletLogger mLogger;
	private final HttpServletRequest mRequest;
	private final String mId;

	public Request(final HttpServletRequest request, final ServletLogger logger) {
		mLogger = logger;
		mParameterList = extractParameter(request);
		mRequest = request;
		mId = getId();
	}

	private Map<String, String[]> extractParameter(final HttpServletRequest request) {
		if (request == null) {
			throw new IllegalArgumentException("The request was null");
		}
		final Map<String, String[]> paramList = new HashMap<>();
		final Enumeration<String> paramNames = request.getParameterNames();
		if (paramNames == null) {
			throw new IllegalArgumentException("No parameter were transmitted (paramNames == null)");
		}
		while (paramNames.hasMoreElements()) {
			final String paramName = paramNames.nextElement();
			final String[] paramValues = request.getParameterValues(paramName);
			paramList.put(paramName, paramValues);

			if (mLogger.isDebugEnabled()) {
				final StringBuilder sb = new StringBuilder();
				sb.append("\t{");
				sb.append(paramName);
				sb.append("} :: {");
				for (final String s : paramValues) {
					sb.append(s);
					sb.append("}");
				}
				mLogger.debug(sb.toString());
			}
		}
		return paramList;
	}

	private String getId() {
		if (getParameterList().containsKey("requestId")) {
			return getSingleParameter("requestId");
		}
		return mRequest.getSession().getId();
	}

	public ServletLogger getLogger() {
		return mLogger;
	}

	public String getRequestId() {
		return mId;
	}

	public HttpSession getSession() {
		return mRequest.getSession();
	}

	public Map<String, String[]> getParameterList() {
		return mParameterList;
	}

	public String getSingleParameter(final String parameterName) throws IllegalArgumentException {
		final String[] parameters = getParameterList().get(parameterName);

		if (parameters == null) {
			throw new IllegalArgumentException("The parameter \"" + parameterName + "\" was not supplied");
		}
		if (parameters.length != 1) {
			throw new IllegalArgumentException("The parameter \"" + parameterName
					+ "\" has an unexpected length (Expected 1, but was " + parameters.length + ")");
		}

		return parameters[0];
	}
}
