package de.uni_freiburg.informatik.ultimate.witnessparser;

import java.io.File;
import java.io.IOException;
import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.UUID;
import java.util.stream.Collectors;

import com.amihaiemil.eoyaml.Node;
import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlInput;
import com.amihaiemil.eoyaml.YamlMapping;
import com.amihaiemil.eoyaml.YamlNode;
import com.amihaiemil.eoyaml.YamlSequence;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Invariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Metadata;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Producer;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Task;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

public class YamlWitnessParser {

	public static Witness parseWitness(final String yamlInput) throws IOException {
		final YamlInput witnessInput = Yaml.createYamlInput(yamlInput);
		return parseWitnessEntries(witnessInput);
	}

	public static Witness parseWitness(final File yamlInput) throws IOException {
		final YamlInput witnessInput = Yaml.createYamlInput(yamlInput);
		return parseWitnessEntries(witnessInput);
	}

	private static Witness parseWitnessEntries(final YamlInput witnessInput) throws IOException {
		final YamlSequence witnessEntries = witnessInput.readYamlSequence();
		final List<WitnessEntry> entries = new ArrayList<>();

		for (final YamlNode witnessEntry : witnessEntries) {
			final WitnessEntry newEntry = parseWitnessEntry(witnessEntry);
			entries.add(newEntry);
		}

		return new Witness(entries);
	}

	private static WitnessEntry parseWitnessEntry(final YamlNode entry) {

		assert (entry.type() == Node.MAPPING);

		final YamlMapping entryMapping = entry.asMapping();
		final String entryType = entryMapping.string("entry_type");

		if (entryType.equals(LocationInvariant.NAME)) {

			final Metadata metadata = YamlWitnessParser.parseMetadata(entry);
			final Location location = YamlWitnessParser.parseLocation(entry);
			final Invariant locationInvariant = parseInvariant(entry, LocationInvariant.NAME);

			return new LocationInvariant(metadata, location, locationInvariant);

		}
		if (entryType.equals(LoopInvariant.NAME)) {

			final Metadata metadata = YamlWitnessParser.parseMetadata(entry);
			final Location location = YamlWitnessParser.parseLocation(entry);
			final Invariant loopInvariant = parseInvariant(entry, LoopInvariant.NAME);

			return new LoopInvariant(metadata, location, loopInvariant);

		}
		// In this case, throw exception -Katie
		throw new UnsupportedOperationException("Unknown entry type");
	}

	private static Metadata parseMetadata(final YamlNode entry) {
		// Method parses metadata mapping from an entry and return new Metadata(...) object

		assert (entry.type() == Node.MAPPING);

		final YamlMapping entryMapping = entry.asMapping();
		final YamlMapping metadataEntry = entryMapping.yamlMapping("metadata");

		final FormatVersion formatVersion = FormatVersion.fromString(metadataEntry.string("format_version"));
		final UUID uuid = UUID.fromString(metadataEntry.string("uuid"));
		final OffsetDateTime creationTime = OffsetDateTime.parse(metadataEntry.string("creation_time"));

		return new Metadata(formatVersion, uuid, creationTime, parseProducer(metadataEntry), parseTask(metadataEntry));
	}

	private static Producer parseProducer(final YamlMapping entry) {
		final YamlMapping producerMapping = entry.asMapping().value("producer").asMapping();
		// TODO: I don't see any reason to parse the optional entries here...
		return new Producer(producerMapping.string("name"), producerMapping.string("version"));
	}

	private static Task parseTask(final YamlNode entry) {
		final YamlMapping taskMapping = entry.asMapping().value("task").asMapping();
		final List<String> files = taskMapping.yamlSequence("input_files").values().stream()
				.map(x -> x.asScalar().value()).collect(Collectors.toList());
		final var hashesRaw = taskMapping.yamlMapping("input_file_hashes");
		final Map<String, String> hashes = hashesRaw.keys().stream()
				.collect(Collectors.toMap(x -> x.asScalar().value(), x -> hashesRaw.string(x)));
		final String spec = taskMapping.string("specification");
		final String dataModel = taskMapping.string("data_model");
		final String language = taskMapping.string("language");
		return new Task(files, hashes, spec, dataModel, language);
	}

	private static Location parseLocation(final YamlNode entry) {

		final YamlNode locationEntry = entry.asMapping().value("location");
		final YamlMapping locationMapping = locationEntry.asMapping();

		final String fileName = locationMapping.string("file_name");
		final String fileHash = locationMapping.string("file_hash");
		final int line = locationMapping.integer("line");
		final int column = locationMapping.integer("column");
		final String function = locationMapping.string("function");

		return new Location(fileName, fileHash, line, column, function);
	}

	private static Invariant parseInvariant(final YamlNode entry, final String name) {
		// this method parses an invariant mapping from an entry called 'name' and return new Invariant(...) object
		final YamlNode invariantEntry = entry.asMapping().value(name);
		final YamlMapping invariantMapping = invariantEntry.asMapping();

		final String expression = invariantMapping.string("string");
		final String type = invariantMapping.string("type");
		final String format = invariantMapping.string("format");

		return new Invariant(expression, type, format);
	}
}
