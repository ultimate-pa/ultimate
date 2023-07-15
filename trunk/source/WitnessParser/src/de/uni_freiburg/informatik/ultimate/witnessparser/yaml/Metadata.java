package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.Date;
import java.util.UUID;

public class Metadata {

	final FormatVersion mFormatVersion;
	final UUID mUuid;
	final Date mCreationTime;
	final Producer mProducer;

	public Metadata(final FormatVersion formatVersion, final UUID uuid, final Date creationTime,
			final Producer producer) {
		mFormatVersion = formatVersion;
		mUuid = uuid;
		mCreationTime = creationTime;
		mProducer = producer;
	}

	public FormatVersion getFormatVersion() {
		return mFormatVersion;
	}

	public UUID getUuid() {
		return mUuid;
	}

	public Date getCreationTime() {
		return mCreationTime;
	}

	public Producer getProducer() {
		return mProducer;
	}

	// TODO: Add "task" metadata
}
