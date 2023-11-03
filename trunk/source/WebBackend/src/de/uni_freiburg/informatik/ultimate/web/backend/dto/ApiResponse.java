package de.uni_freiburg.informatik.ultimate.web.backend.dto;

import java.io.IOException;
import java.io.Serializable;
import java.util.Objects;

import javax.servlet.http.HttpServletResponse;

import com.google.gson.Gson;
import com.google.gson.annotations.SerializedName;
import com.google.gson.stream.JsonWriter;

public class ApiResponse implements Serializable {

	public enum ApiResponseStatus {
		SUCCESS, ERROR
	}

	private static final long serialVersionUID = 1L;

	@SerializedName("status")
	private String mStatus;

	public ApiResponse() {
		mStatus = ApiResponseStatus.SUCCESS.name();
	}

	public void write(final HttpServletResponse response) throws IOException {
		response.setContentType("application/json");
		response.setCharacterEncoding("UTF-8");
		final JsonWriter jsonWriter = new JsonWriter(response.getWriter());
		jsonWriter.jsonValue(new Gson().toJson(this));
	}

	private void setStatus(final ApiResponseStatus status) {
		mStatus = status.name();
	}

	public void setStatus(final String status) {
		mStatus = Objects.requireNonNull(status);
	}

	public void setStatusError() {
		setStatus(ApiResponseStatus.ERROR);
	}

	public void setStatusSuccess() {
		setStatus(ApiResponseStatus.SUCCESS);
	}
}
