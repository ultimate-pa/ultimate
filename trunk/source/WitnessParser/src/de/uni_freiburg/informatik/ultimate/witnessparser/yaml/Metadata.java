package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.time.OffsetDateTime;
import java.time.temporal.ChronoUnit;
import java.util.UUID;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;

public class Metadata implements IYamlProvider {

	private final FormatVersion mFormatVersion;
	private final UUID mUuid;
	private final OffsetDateTime mCreationTime;
	private final Producer mProducer;
	private final Task mTask;

	public Metadata(final FormatVersion formatVersion, final UUID uuid, final OffsetDateTime creationTime,
			final Producer producer, final Task task) {
		mFormatVersion = formatVersion;
		mUuid = uuid;
		mCreationTime = creationTime;
		mProducer = producer;
		mTask = task;
	}

	public FormatVersion getFormatVersion() {
		return mFormatVersion;
	}

	public UUID getUuid() {
		return mUuid;
	}

	public OffsetDateTime getCreationTime() {
		return mCreationTime;
	}

	public Producer getProducer() {
		return mProducer;
	}

	@Override
	public YamlNode toYaml() {
		return Yaml.createYamlMappingBuilder().add("format_version", mFormatVersion.toString())
				.add("uuid", mUuid.toString())
				.add("creation_time", mCreationTime.truncatedTo(ChronoUnit.SECONDS).toString())
				.add("producer", mProducer.toYaml()).add("task", mTask.toYaml()).build();
	}
}
