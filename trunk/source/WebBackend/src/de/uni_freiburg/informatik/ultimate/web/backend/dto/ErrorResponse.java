package de.uni_freiburg.informatik.ultimate.web.backend.dto;

import com.google.gson.annotations.SerializedName;

public class ErrorResponse extends ApiResponse {

	private static final long serialVersionUID = 1L;

	@SerializedName("msg")
	private final String mMessage;

	public ErrorResponse(final String message) {
		setStatusError();
		mMessage = message;
	}
}
