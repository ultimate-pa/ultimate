package de.uni_freiburg.informatik.ultimate.version;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public class UltimateVersion {

	/**
	 * Get the current Git version string of the Ultimate framework.
	 *
	 * @return String describing the version of the current Git repository or null if version.properties does not exist.
	 */
	public static String getGitVersion() {
		final Properties properties = new Properties();
		final String unknown = "?";
		final String dirtyFormat = "%s-%s-m";
		try {
			final InputStream prop = UltimateVersion.class.getClassLoader().getResourceAsStream("version.properties");
			if (prop == null) {
				return String.format(dirtyFormat, unknown, unknown);
			}
			properties.load(prop);
		} catch (final IOException e) {
			return null;
		}

		final String branch = properties.getProperty("git.branch", unknown).replace('/', '.');
		final String fullHash = properties.getProperty("git.commit.id", unknown).replace('/', '.');
		final String hash = properties.getProperty("git.commit.id.abbrev", unknown);
		final String dirty = properties.getProperty("git.dirty", unknown);

		final String actualBranch;
		if (fullHash.equals(branch)) {
			actualBranch = unknown;
		} else {
			actualBranch = branch;
		}

		final String format;
		if ("true".equals(dirty)) {
			format = dirtyFormat;
		} else {
			format = "%s-%s";
		}
		return String.format(format, actualBranch, hash);
	}

}
