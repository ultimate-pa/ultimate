/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 *
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter.yaml;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FunctionContract;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.GhostVariable;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

/**
 * Exports a witness for the format version 2.x to YAML. The format 2.0 is described here:
 * https://sosy-lab.gitlab.io/benchmarking/sv-witnesses/yaml/correctness-witnesses.html <br>
 * Additionally we also export function contracts for version 2.1, and allow witnesses with ghost variables.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class YamlWitnessWriterV2 extends YamlWitnessWriter {
	private final MetadataProvider mMetadataProvider;
	private final boolean mWriteFunctionContracts;
	private final boolean mAllowGhostVariables;

	public YamlWitnessWriterV2(final MetadataProvider metadataProvider, final boolean writeFunctionContracts,
			final boolean allowGhostVariables) {
		mMetadataProvider = metadataProvider;
		mWriteFunctionContracts = writeFunctionContracts;
		mAllowGhostVariables = allowGhostVariables;
	}

	@Override
	public String toString(final Witness witness) {
		final List<Map<String, Object>> resultEntries = new ArrayList<>();
		final List<Map<String, Object>> content = witness.getEntries().stream()
				.filter(x -> x instanceof LoopInvariant || x instanceof LocationInvariant
						|| (mWriteFunctionContracts && x instanceof FunctionContract))
				.map(this::asContentMap).collect(Collectors.toList());
		final Map<String, Object> invariantSet = new LinkedHashMap<>();
		invariantSet.put("entry_type", "invariant_set");
		invariantSet.put("metadata", mMetadataProvider.getFreshMetadata());
		invariantSet.put("content", content);
		resultEntries.add(invariantSet);
		final List<Map<String, Object>> ghostVariables = extractGhostVariables(witness);
		if (!ghostVariables.isEmpty()) {
			if (!mAllowGhostVariables) {
				throw new UnsupportedOperationException("Unsupported witness format for ghost variables");
			}
			final Map<String, Object> ghostInstrumentation = new LinkedHashMap<>();
			ghostInstrumentation.put("entry_type", "ghost_instrumentation");
			ghostInstrumentation.put("metadata", mMetadataProvider.getFreshMetadata());
			final LinkedHashMap<String, Object> ghostContent = new LinkedHashMap<>();
			ghostContent.put("ghost_variables", ghostVariables);
			ghostContent.put("ghost_updates", extractGhostUpdates(witness));
			ghostInstrumentation.put("content", ghostContent);
			resultEntries.add(ghostInstrumentation);
		}
		return formatYaml(resultEntries);
	}

	private static List<Map<String, Object>> extractGhostVariables(final Witness witness) {
		return witness.getEntries().stream().filter(GhostVariable.class::isInstance)
				.map(x -> extractGhostVariableMap((GhostVariable) x)).collect(Collectors.toList());
	}

	private static List<Map<String, Object>> extractGhostUpdates(final Witness witness) {
		// Group ghost updates by location first
		final Map<Location, List<GhostUpdate>> locs2Updates = new HashMap<>();
		for (final var entry : witness.getEntries()) {
			if (!(entry instanceof GhostUpdate)) {
				continue;
			}
			final GhostUpdate update = (GhostUpdate) entry;
			locs2Updates.computeIfAbsent(update.getLocation(), x -> new ArrayList<>()).add(update);
		}
		final List<Map<String, Object>> result = new ArrayList<>();
		for (final var entry : locs2Updates.entrySet()) {
			final Map<String, Object> map = new LinkedHashMap<>();
			map.put("location", entry.getKey());
			final List<Map<String, String>> updateMap = entry.getValue().stream()
					.map(YamlWitnessWriterV2::extractGhostUpdateMap).collect(Collectors.toList());
			map.put("updates", updateMap);
			result.add(map);
		}
		return result;
	}

	private static Map<String, String> extractGhostUpdateMap(final GhostUpdate update) {
		final Map<String, String> result = new LinkedHashMap<>();
		result.put("variable", update.getName());
		result.put("value", update.getValue());
		result.put("format", update.getValueFormat());
		return result;
	}

	private static Map<String, Object> extractGhostVariableMap(final GhostVariable variable) {
		final Map<String, Object> result = new LinkedHashMap<>();
		result.put("name", variable.getVariable());
		result.put("type", variable.getType());
		result.put("scope", variable.getScope());
		final Map<String, String> initial = new LinkedHashMap<>();
		initial.put("value", variable.getInitialValue());
		initial.put("format", variable.getValueFormat());
		result.put("initial", initial);
		return result;
	}

	private Map<String, Object> asContentMap(final WitnessEntry entry) {
		final Map<String, Object> content = new LinkedHashMap<>();
		content.put("type", entry.getName());
		if (entry instanceof LoopInvariant) {
			final LoopInvariant loopInvariant = (LoopInvariant) entry;
			content.put("location", loopInvariant.getLocation().toMap());
			content.put("value", loopInvariant.getInvariant());
			content.put("format", loopInvariant.getFormat());
		} else if (entry instanceof LocationInvariant) {
			final LocationInvariant locationInvariant = (LocationInvariant) entry;
			content.put("location", locationInvariant.getLocation().toMap());
			content.put("value", locationInvariant.getInvariant());
			content.put("format", locationInvariant.getFormat());
		} else if (entry instanceof FunctionContract) {
			final FunctionContract contract = (FunctionContract) entry;
			content.put("location", contract.getLocation().toMap());
			if (contract.getRequires() != null) {
				content.put("requires", contract.getRequires());
			}
			if (contract.getEnsures() != null) {
				content.put("ensures", contract.getEnsures());
			}
			content.put("format", contract.getFormat());
		} else {
			throw new UnsupportedOperationException("Unknown entry type " + entry.getClass().getSimpleName());
		}
		return Map.of("invariant", content);
	}
}
