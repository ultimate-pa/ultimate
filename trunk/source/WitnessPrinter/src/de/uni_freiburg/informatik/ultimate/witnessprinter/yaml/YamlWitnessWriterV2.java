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

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FunctionContract;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

/**
 * Exports a witness for the format version 2.x to YAML. The format 2.0 is described here:
 * https://sosy-lab.gitlab.io/benchmarking/sv-witnesses/yaml/correctness-witnesses.html <br>
 * Additionally we also export function contracts for version 2.1.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class YamlWitnessWriterV2 extends YamlWitnessWriter {
	private final MetadataProvider mMetadataProvider;
	private final boolean mWriteFunctionContracts;

	public YamlWitnessWriterV2(final MetadataProvider metadataProvider, final boolean writeFunctionContracts) {
		mMetadataProvider = metadataProvider;
		mWriteFunctionContracts = writeFunctionContracts;
	}

	@Override
	public String toString(final Witness witness) {
		final List<Map<String, Object>> content = witness.getEntries().stream()
				.filter(x -> x instanceof LoopInvariant || x instanceof LocationInvariant
						|| (mWriteFunctionContracts && x instanceof FunctionContract))
				.map(this::asContentMap).collect(Collectors.toList());
		final Map<String, Object> invariantSet = new LinkedHashMap<>();
		invariantSet.put("entry_type", "invariant_set");
		invariantSet.put("metadata", mMetadataProvider.getFreshMetadata());
		invariantSet.put("content", content);
		return formatYaml(List.of(invariantSet));
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
