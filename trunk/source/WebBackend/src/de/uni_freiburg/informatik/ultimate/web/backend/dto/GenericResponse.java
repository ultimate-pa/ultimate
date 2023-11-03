package de.uni_freiburg.informatik.ultimate.web.backend.dto;

import com.google.gson.annotations.SerializedName;

public class GenericResponse extends ApiResponse {

	private static final long serialVersionUID = 1L;

	@SerializedName("msg")
	private final String mMessage;

	public GenericResponse(final String message) {
		mMessage = message;
	}
}
