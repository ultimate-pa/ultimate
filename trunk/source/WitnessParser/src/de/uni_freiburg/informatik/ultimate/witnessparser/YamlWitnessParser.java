/*
 * Copyright (C) 2023 Manuel Bentele (bentele@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Katie Kowalyshyn (kakowalyshyn@davidson.edu)
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessParser plug-in.
 *
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessparser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.time.OffsetDateTime;
import java.time.ZoneId;
import java.util.Date;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.yaml.snakeyaml.LoaderOptions;
import org.yaml.snakeyaml.Yaml;
import org.yaml.snakeyaml.constructor.SafeConstructor;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FunctionContract;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.GhostVariable;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Invariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Metadata;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Producer;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Task;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

/**
 * Class to parse witnesses, i.e. read the from a string or file and transform them to the internal {@link Witness} data
 * structure.
 *
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 * @author Katie Kowalyshyn (kakowalyshyn@davidson.edu)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class YamlWitnessParser {
	private static final Set<String> ENTRIES_BEFORE_V3 = Set.of(LoopInvariant.NAME, LocationInvariant.NAME);

	// Maximal size for witnesses to be parsed
	// The default is just 3MB, but this is not sufficient for us.
	private static final int MAXIMAL_SIZE = 50 * 1024 * 1024;

	public static Witness parseWitness(final File yamlInput) throws IOException {
		final LoaderOptions loaderOptions = new LoaderOptions();
		loaderOptions.setCodePointLimit(MAXIMAL_SIZE);
		final List<Map<String, Object>> res =
				new Yaml(new SafeConstructor(loaderOptions)).load(new FileInputStream(yamlInput));
		return new Witness(res.stream().flatMap(YamlWitnessParser::parseWitnessEntry).collect(Collectors.toList()));
	}

	@SuppressWarnings("unchecked")
	private static Stream<WitnessEntry> parseWitnessEntry(final Map<String, Object> entry) {
		final Metadata metadata = parseMetadata((Map<String, Object>) entry.get("metadata"));
		final FormatVersion formatVersion = metadata.getFormatVersion();
		switch ((String) entry.get("entry_type")) {
		case LocationInvariant.NAME: {
			if (formatVersion.getMajor() != 0) {
				throw new UnsupportedOperationException(
						LocationInvariant.NAME + " is only allowed in format version 0.x");
			}
			final Location location = parseLocation((Map<String, Object>) entry.get("location"));
			final Invariant locationInvariant = parseInvariant((Map<String, String>) entry.get(LocationInvariant.NAME));
			return Stream.of(new LocationInvariant(metadata, location, locationInvariant));
		}
		case LoopInvariant.NAME: {
			if (formatVersion.getMajor() != 0) {
				throw new UnsupportedOperationException(LoopInvariant.NAME + " is only allowed in format version 0.x");
			}
			final Location location = parseLocation((Map<String, Object>) entry.get("location"));
			final Invariant loopInvariant = parseInvariant((Map<String, String>) entry.get(LoopInvariant.NAME));
			return Stream.of(new LoopInvariant(metadata, location, loopInvariant));
		}
		case GhostVariable.NAME: {
			final String variable = (String) entry.get("variable");
			final String initial = (String) entry.get("initial");
			final String scope = (String) entry.get("scope");
			final String type = (String) entry.get("type");
			return Stream.of(new GhostVariable(metadata, variable, initial, scope, type));
		}
		case GhostUpdate.NAME: {
			final Location location = parseLocation((Map<String, Object>) entry.get("location"));
			final String variable = (String) entry.get("variable");
			final String expression = (String) entry.get("expression");
			return Stream.of(new GhostUpdate(metadata, variable, expression, location));
		}
		case "invariant_set": {
			if (formatVersion.getMajor() != 2) {
				throw new UnsupportedOperationException("invariant_set is only allowed in format version 2.x");
			}
			// TODO: This just transforms the "new" format to the "old" format, maybe change this in the future
			final List<Map<String, Map<String, Object>>> content =
					(List<Map<String, Map<String, Object>>>) entry.get("content");
			return content.stream().map(x -> parseAsSingleEntry(x.get("invariant"), metadata));
		}
		case "entry_set": {
			if (formatVersion.getMajor() < 3) {
				throw new UnsupportedOperationException("entry_set is only allowed in format version >=3.x");
			}
			// TODO: This just transforms the "new" format to the "old" format, maybe change this in the future
			final List<Map<String, Object>> content = (List<Map<String, Object>>) entry.get("content");
			return content.stream().map(x -> parseAsSingleEntry(x, metadata));
		}
		default:
			throw new UnsupportedOperationException("Unknown entry type " + entry.get("entry_type"));
		}
	}

	@SuppressWarnings("unchecked")
	private static WitnessEntry parseAsSingleEntry(final Map<String, Object> setEntry, final Metadata metadata) {
		// Create new metadata with a fresh UUID (because we rely on it as a unique identifier)
		final Metadata newMetadata = new Metadata(metadata.getFormatVersion(), UUID.randomUUID(),
				metadata.getCreationTime(), metadata.getProducer(), metadata.getTask());
		final String format = (String) setEntry.get("format");
		final String type = (String) setEntry.get("type");
		if (metadata.getFormatVersion().getMajor() < 3 && !ENTRIES_BEFORE_V3.contains(type)) {
			throw new UnsupportedOperationException(
					String.format("The type %s is only allowed in format version >=3.x", type));
		}
		switch (type) {
		case LocationInvariant.NAME: {
			final Location location = parseLocation((Map<String, Object>) setEntry.get("location"));
			final Invariant invariant = new Invariant((String) setEntry.get("value"), "assertion", format);
			return new LocationInvariant(newMetadata, location, invariant);
		}
		case LoopInvariant.NAME: {
			final Location location = parseLocation((Map<String, Object>) setEntry.get("location"));
			final Invariant invariant = new Invariant((String) setEntry.get("value"), "assertion", format);
			return new LoopInvariant(newMetadata, location, invariant);
		}
		case FunctionContract.NAME: {
			final Location location = parseLocation((Map<String, Object>) setEntry.get("location"));
			return new FunctionContract(newMetadata, location, (List<String>) setEntry.get("requires"),
					(List<String>) setEntry.get("ensures"), format);
		}
		case GhostVariable.NAME:
			return new GhostVariable(newMetadata, (String) setEntry.get("variable"), (String) setEntry.get("initial"),
					(String) setEntry.get("scope"), (String) setEntry.get("c_type"));
		case GhostUpdate.NAME: {
			final Location location = parseLocation((Map<String, Object>) setEntry.get("location"));
			return new GhostUpdate(newMetadata, (String) setEntry.get("variable"), (String) setEntry.get("value"),
					location);
		}
		default:
			throw new UnsupportedOperationException("Unknown entry type " + setEntry.get("type"));
		}
	}

	@SuppressWarnings("unchecked")
	private static Metadata parseMetadata(final Map<String, Object> metadata) {
		final FormatVersion formatVersion = FormatVersion.fromString(metadata.get("format_version").toString());
		final UUID uuid = UUID.fromString((String) metadata.get("uuid"));
		final Object rawDate = metadata.get("creation_time");
		final OffsetDateTime creationTime;
		if (rawDate instanceof Date) {
			creationTime = OffsetDateTime.ofInstant(((Date) rawDate).toInstant(), ZoneId.systemDefault());
		} else {
			creationTime = OffsetDateTime.parse((String) rawDate);
		}
		final Producer producer = parseProducer((Map<String, String>) metadata.get("producer"));
		final Task task = parseTask((Map<String, Object>) metadata.get("task"));
		return new Metadata(formatVersion, uuid, creationTime, producer, task);
	}

	private static Producer parseProducer(final Map<String, String> producer) {
		// TODO: I don't see any reason to parse the optional entries here...
		return new Producer(producer.get("name"), producer.get("version"));
	}

	@SuppressWarnings("unchecked")
	private static Task parseTask(final Map<String, Object> task) {
		final List<String> files = (List<String>) task.get("input_files");
		final Map<String, String> hashes = (Map<String, String>) task.get("input_file_hashes");
		final String spec = (String) task.get("specification");
		final String dataModel = (String) task.get("data_model");
		final String language = (String) task.get("language");
		return new Task(files, hashes, spec, dataModel, language);
	}

	private static Location parseLocation(final Map<String, Object> location) {
		return new Location((String) location.get("file_name"), (String) location.get("file_hash"),
				(Integer) location.get("line"), (Integer) location.get("column"), (String) location.get("function"));
	}

	private static Invariant parseInvariant(final Map<String, String> invariant) {
		return new Invariant(invariant.get("string"), invariant.get("type"), invariant.get("format"));
	}
}
