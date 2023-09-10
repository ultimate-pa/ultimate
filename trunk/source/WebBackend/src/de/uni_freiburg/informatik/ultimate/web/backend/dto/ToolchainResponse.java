package de.uni_freiburg.informatik.ultimate.web.backend.dto;

import java.io.IOException;
import java.util.List;
import java.util.Optional;

import com.google.gson.annotations.SerializedName;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.web.backend.util.JobResultStore;

public class ToolchainResponse extends ApiResponse {

	private static final long serialVersionUID = 1L;

	@SerializedName("requestId")
	private final String mRequestId;

	@SerializedName("results")
	private List<UltimateResult> mResults;

	@SerializedName("error")
	private String mErrorMessage;

	public ToolchainResponse(final String requestId) {
		mRequestId = requestId;
		setStatus("scheduled");
	}

	public void setResults(final List<UltimateResult> results) {
		mResults = results;
	}

	public void setErrorMessage(final String msg) {
		setStatusError();
		mErrorMessage = msg;
	}

	public void store(final ILogger logger) throws IOException {
		final JobResultStore jobResult = new JobResultStore(logger, mRequestId);
		jobResult.store(this);
	}

	public static Optional<ToolchainResponse> load(final ILogger logger, final String requestId) {
		final JobResultStore jobResult = new JobResultStore(logger, requestId);
		return jobResult.load(ToolchainResponse.class);
	}
}
