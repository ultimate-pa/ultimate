package de.uni_freiburg.informatik.ultimate.webinterface;

import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;

import javax.servlet.http.HttpServletRequest;

public class Request {
	private final Map<String, String[]> mParameterList;
	private final ServletLogger mLogger;
	private final HttpServletRequest mRequest;

	Request(final HttpServletRequest request, final ServletLogger logger) {
		mLogger = logger;
		mParameterList = extractParameter(request);
		mRequest = request;
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
				mLogger.logDebug(sb.toString());
			}
		}
		return paramList;
	}

	public ServletLogger getLogger() {
		return mLogger;
	}

	public String getRequestId() {
		return mRequest.getSession().getId();
	}

	public Map<String, String[]> getParameterList() {
		return mParameterList;
	}
}
