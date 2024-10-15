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
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.yaml.snakeyaml.LoaderOptions;
import org.yaml.snakeyaml.Yaml;
import org.yaml.snakeyaml.constructor.SafeConstructor;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FunctionContract;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.GhostVariable;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
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
		switch ((String) entry.get("entry_type")) {
		case LocationInvariant.NAME: {
			final Location location = parseLocation((Map<String, Object>) entry.get("location"));
			final Map<String, String> invariant = (Map<String, String>) entry.get(LocationInvariant.NAME);
			return Stream.of(new LocationInvariant(location, invariant.get("string"), invariant.get("format")));
		}
		case LoopInvariant.NAME: {
			final Location location = parseLocation((Map<String, Object>) entry.get("location"));
			final Map<String, String> invariant = (Map<String, String>) entry.get(LoopInvariant.NAME);
			return Stream.of(new LoopInvariant(location, invariant.get("string"), invariant.get("format")));
		}
		case "ghost_instrumentation": {
			final var content = (Map<String, List<Map<String, Object>>>) entry.get("content");
			final List<Map<String, Object>> ghostVariables = content.get("ghost_variables");
			final List<Map<String, Object>> ghostUpdates = content.get("ghost_updates");
			return Stream.concat(ghostVariables.stream().map(x -> parseGhostVariable(x)),
					ghostUpdates.stream().flatMap(x -> parseGhostUpdates(x)));
		}
		case "invariant_set": {
			final List<Map<String, Map<String, Object>>> content =
					(List<Map<String, Map<String, Object>>>) entry.get("content");
			return content.stream().map(x -> parseInvariantSetEntry(x));
		}
		default:
			throw new UnsupportedOperationException("Unknown entry type " + entry.get("entry_type"));
		}
	}

	@SuppressWarnings("unchecked")
	private static GhostVariable parseGhostVariable(final Map<String, Object> entry) {
		final var initial = (Map<String, String>) entry.get("initial");
		return new GhostVariable((String) entry.get("name"), initial.get("value"), initial.get("format"),
				(String) entry.get("scope"), (String) entry.get("type"));
	}

	@SuppressWarnings("unchecked")
	private static Stream<GhostUpdate> parseGhostUpdates(final Map<String, Object> entry) {
		final Location location = parseLocation((Map<String, Object>) entry.get("location"));
		final List<Map<String, String>> updates = (List<Map<String, String>>) entry.get("updates");
		return updates.stream().map(x -> new GhostUpdate(x.get("variable"), x.get("value"), x.get("format"), location));
	}

	@SuppressWarnings("unchecked")
	private static WitnessEntry parseInvariantSetEntry(final Map<String, Map<String, Object>> entry) {
		if (entry.size() != 1) {
			throw new UnsupportedOperationException("Invalid entry in content " + entry);
		}
		final var map = entry.values().iterator().next();
		final Location location = parseLocation((Map<String, Object>) map.get("location"));
		final String format = (String) map.get("format");
		switch ((String) map.get("type")) {
		case LocationInvariant.NAME:
			return new LocationInvariant(location, (String) map.get("value"), format);
		case LoopInvariant.NAME:
			return new LoopInvariant(location, (String) map.get("value"), format);
		case FunctionContract.NAME:
			return new FunctionContract(location, (String) map.get("requires"), (String) map.get("ensures"), format);
		default:
			throw new UnsupportedOperationException("Invalid entry in content" + entry);
		}
	}

	private static Location parseLocation(final Map<String, Object> location) {
		return new Location((String) location.get("file_name"), (String) location.get("file_hash"),
				(Integer) location.get("line"), (Integer) location.get("column"), (String) location.get("function"));
	}
}
