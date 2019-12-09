package de.uni_freiburg.informatik.ultimate.web.backend.util;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Optional;

import com.google.gson.Gson;
import com.google.gson.stream.JsonReader;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class JobResultStore {
	private final String mJobId;
	private final ILogger mLogger;

	public JobResultStore(final ILogger logger, final String jobId) {
		mJobId = jobId;
		validateJobId();
		mLogger = logger;
	}

	private void validateJobId() {
		final String cleanedId = mJobId.replaceAll("\\W+", "");
		if (!cleanedId.equals(mJobId)) {
			throw new IllegalArgumentException("Job ID contained illegal characters");
		}
	}

	public void store(final Object obj) throws IOException {
		if (obj == null) {
			throw new IllegalStateException("No JSON payload");
		}
		final File file = getJsonFile();
		mLogger.info("Storing job results to: %s", file);
		try (final BufferedWriter writer = new BufferedWriter(new FileWriter(file))) {
			writer.write(new Gson().toJson(obj));
		}
	}

	public <T> Optional<T> load(final Class<T> clazz) {
		try {
			final JsonReader reader = new JsonReader(new FileReader(getJsonFile()));
			return Optional.of(new Gson().fromJson(reader, clazz));
		} catch (final IOException e) {
			return Optional.empty();
		}
	}

	private File getJsonFile() {
		return FileUtil.getJobResultJsonFile(mJobId);
	}

}
