package de.uni_freiburg.informatik.ultimate.witnessparser;

import java.io.File;
import java.io.IOException;

import com.amihaiemil.eoyaml.Node;
import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlInput;
import com.amihaiemil.eoyaml.YamlMapping;
import com.amihaiemil.eoyaml.YamlNode;
import com.amihaiemil.eoyaml.YamlSequence;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Invariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Metadata;
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
		final Witness witness = new Witness();

		for (final YamlNode witnessEntry : witnessEntries) {
			final WitnessEntry newEntry = parseWitnessEntry(witnessEntry);
			witness.add(newEntry);
		}

		return witness;
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

		} else if (entryType.equals(LoopInvariant.NAME)) {

			final Metadata metadata = YamlWitnessParser.parseMetadata(entry);
			final Location location = YamlWitnessParser.parseLocation(entry);
			final Invariant loopInvariant = parseInvariant(entry, LoopInvariant.NAME);

			return new LoopInvariant(metadata, location, loopInvariant);

		} else {
			// TODO: Unknown entry type
			return null;
		}
	}

	private static Metadata parseMetadata(final YamlNode entry) {
		// TODO: parse metadata mapping from an entry and return new Metadata(...)
		// object
		return null;
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
		// TODO: parse invariant mapping from an entry called 'name' and return new
		// Invariant(...) object
		return null;
	}
}
