package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

public class Producer {
	private final String mName;
	private final String mVersion;
	private final String mConfiguration;
	private final String mDescription;
	private final String mCommandLine;

	public Producer(final String name, final String version) {
		this(name, version, null, null, null);
	}

	public Producer(final String name, final String version, final String configuration, final String description,
			final String commandLine) {
		mName = name;
		mVersion = version;
		mConfiguration = configuration;
		mDescription = description;
		mCommandLine = commandLine;
	}

	public String getName() {
		return mName;
	}

	public String getVersion() {
		return mVersion;
	}

	public String getConfiguration() {
		return mConfiguration;
	}

	public String getDescription() {
		return mDescription;
	}

	public String getCommandLine() {
		return mCommandLine;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}

		if (obj instanceof Producer) {
			final Producer other = Producer.class.cast(obj);
			// @formatter:off
			if (this.getName().equals(other.getName()) &&
				this.getVersion().equals(other.getVersion()) &&
				this.getConfiguration().equals(other.getConfiguration()) &&
				this.getDescription().equals(other.getDescription()) &&
				this.getCommandLine().equals(other.getCommandLine())) {

				return true;
			}
			// @formatter:on
		}

		return false;
	}
}
