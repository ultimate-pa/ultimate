package de.uni_freiburg.informatik.ultimate.web.backend.util;

import javax.servlet.http.HttpServletRequest;

public class GetApiRequest {
	private final RessourceType mRessourceType;
	private final TaskType mTaskType;
	private final String[] mUrlParts;

	public GetApiRequest(final HttpServletRequest request) {
		mUrlParts = getUrlParts(request.getPathInfo());
		mRessourceType = setRessource(mUrlParts);
		mTaskType = setTask(mUrlParts);
	}

	private static TaskType setTask(final String[] urlParts) {
		if (urlParts == null || urlParts.length < 3) {
			return TaskType.UNKNOWN;
		}
		switch (urlParts[2]) {
		case "get":
			return TaskType.GET;
		case "delete":
			return TaskType.DELETE;
		default:
			return TaskType.UNKNOWN;
		}
	}

	private static RessourceType setRessource(final String[] urlParts) {
		if (urlParts == null || urlParts.length < 1) {
			return RessourceType.UNKNOWN;
		}

		switch (urlParts[1]) {
		case "job":
			return RessourceType.JOB;
		case "version":
			return RessourceType.VERSION;
		default:
			return RessourceType.UNKNOWN;
		}
	}

	private static String[] getUrlParts(final String pathInfo) {
		return pathInfo != null ? pathInfo.split("/") : null;
	}

	public RessourceType getRessourceType() {
		return mRessourceType;
	}

	public String[] getUrlParts() {
		return mUrlParts;
	}

	public TaskType getTaskType() {
		return mTaskType;
	}
}
