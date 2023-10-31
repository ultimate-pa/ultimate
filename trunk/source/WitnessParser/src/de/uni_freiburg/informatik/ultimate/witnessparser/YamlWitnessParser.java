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
import java.util.List;
import java.util.Map;
import java.util.UUID;
import java.util.stream.Collectors;

import org.yaml.snakeyaml.LoaderOptions;
import org.yaml.snakeyaml.Yaml;
import org.yaml.snakeyaml.constructor.SafeConstructor;

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

/**
 * Class to parse witnesses, i.e. read the from a string or file and transform them to the internal {@link Witness} data
 * structure.
 *
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 * @author Katie Kowalyshyn (kakowalyshyn@davidson.edu)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class YamlWitnessParser {
	// Maximal size for witnesses to be parsed
	// The default is just 3MB, but this is not sufficient for us.
	private static final int MAXIMAL_SIZE = 30 * 1024 * 1024;

	public static Witness parseWitness(final File yamlInput) throws IOException {
		final LoaderOptions loaderOptions = new LoaderOptions();
		loaderOptions.setCodePointLimit(MAXIMAL_SIZE);
		final List<Map<String, Object>> res =
				new Yaml(new SafeConstructor(loaderOptions)).load(new FileInputStream(yamlInput));
		return new Witness(res.stream().map(YamlWitnessParser::parseWitnessEntry).collect(Collectors.toList()));
	}

	private static WitnessEntry parseWitnessEntry(final Map<String, Object> entry) {
		final Metadata metadata = parseMetadata((Map<String, Object>) entry.get("metadata"));
		switch ((String) entry.get("entry_type")) {
		case LocationInvariant.NAME: {
			final Location location = parseLocation((Map<String, Object>) entry.get("location"));
			final Invariant locationInvariant = parseInvariant((Map<String, String>) entry.get(LocationInvariant.NAME));
			return new LocationInvariant(metadata, location, locationInvariant);
		}
		case LoopInvariant.NAME: {
			final Location location = parseLocation((Map<String, Object>) entry.get("location"));
			final Invariant loopInvariant = parseInvariant((Map<String, String>) entry.get(LoopInvariant.NAME));
			return new LoopInvariant(metadata, location, loopInvariant);
		}
		default:
			throw new UnsupportedOperationException("Unknown entry type");
		}
	}

	private static Metadata parseMetadata(final Map<String, Object> metadata) {
		final FormatVersion formatVersion = FormatVersion.fromString(metadata.get("format_version").toString());
		final UUID uuid = UUID.fromString((String) metadata.get("uuid"));
		final OffsetDateTime creationTime = OffsetDateTime.parse((String) metadata.get("creation_time"));
		final Producer producer = parseProducer((Map<String, String>) metadata.get("producer"));
		final Task task = parseTask((Map<String, Object>) metadata.get("task"));
		return new Metadata(formatVersion, uuid, creationTime, producer, task);
	}

	private static Producer parseProducer(final Map<String, String> producer) {
		// TODO: I don't see any reason to parse the optional entries here...
		return new Producer(producer.get("name"), producer.get("version"));
	}

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
