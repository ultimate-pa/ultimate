package de.uni_freiburg.informatik.ultimate.web.backend.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;

import de.uni_freiburg.informatik.ultimate.web.backend.Config;

public class FileUtil {

	private FileUtil() {
		// do not instantiate utility class
	}

	public static File getJobResultJsonFile(final String jobId) {
		return Path.of(Config.TMP_DIR).resolve(jobId + ".result.json").toFile();
	}

	public static File getTmpDir() {
		return Path.of(Config.TMP_DIR).toFile();
	}

	/**
	 * Creates a file in the default temporary-file.
	 *
	 * @param name
	 *            The name of the file (without file extension).
	 * @param content
	 *            Content to end up in the file.
	 * @return
	 * @throws IOException
	 */
	public static File writeTemporaryFile(final String name, final String content) throws IOException {
		final File file = FileUtil.getTmpDir().toPath().resolve(name).toFile();
		try (final Writer fstream = new OutputStreamWriter(new FileOutputStream(file), StandardCharsets.UTF_8)) {
			fstream.write(content);
		}
		return file;
	}

}
