package de.uni_freiburg.informatik.ultimate.website;

import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;

import javax.servlet.http.HttpServletRequest;

public class Request {
	private final Map<String, String[]> mParameterList;
	private final ServletLogger mLogger;
	private final HttpServletRequest mRequest;

	Request(HttpServletRequest request, ServletLogger logger) {
		mLogger = logger;
		mParameterList = extractParameter(request);
		mRequest = request;
	}

	private Map<String, String[]> extractParameter(HttpServletRequest request) {
		if (request == null) {
			throw new IllegalArgumentException("The request was null");
		}
		Map<String, String[]> paramList = new HashMap<String, String[]>();
		Enumeration<String> paramNames = request.getParameterNames();
		if(paramNames == null){
			throw new IllegalArgumentException("No parameter were transmitted (paramNames == null)");
		}
		while (paramNames.hasMoreElements()) {
			String paramName = paramNames.nextElement();
			String[] paramValues = request.getParameterValues(paramName);
			paramList.put(paramName, paramValues);

			if (mLogger.isDebugEnabled()) {
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
	
	public ServletLogger getLogger(){
		return mLogger;
	}
	
	public String getRequestId(){
		return mRequest.getSession().getId();
	}

	public Map<String, String[]> getParameterList() {
		return mParameterList;
	}

	public boolean containsKey(String key) {
		return getParameterList().containsKey(key);
	}

	public String[] get(String key) {
		return getParameterList().get(key);
	}
}
