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
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

/**
 * Exports a witness for the format version 0.1 to YAML (that is no more used in SV-COMP). The exported witness only
 * contains location invariants and loop invariants. See the documentation:
 * https://gitlab.com/sosy-lab/benchmarking/sv-witnesses/-/blob/da1bf387/doc/README-YAML.md
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class YamlWitnessWriterV0 extends YamlWitnessWriter {
	@Override
	public String toString(final Witness witness) {
		return formatYaml(
				witness.getEntries().stream().filter(x -> x instanceof LoopInvariant || x instanceof LocationInvariant)
						.map(this::toMap).collect(Collectors.toList()));
	}

	private Map<String, Object> toMap(final WitnessEntry entry) {
		if (entry instanceof LoopInvariant) {
			final LoopInvariant loopInvariant = (LoopInvariant) entry;
			final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
			result.put("entry_type", entry.getName());
			result.put("metadata", loopInvariant.getMetadata().toMap());
			result.put("location", loopInvariant.getLocation().toMap());
			result.put(entry.getName(), loopInvariant.getInvariant().toMap());
			return result;
		}
		if (entry instanceof LocationInvariant) {
			final LocationInvariant locationInvariant = (LocationInvariant) entry;
			final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
			result.put("entry_type", entry.getName());
			result.put("metadata", locationInvariant.getMetadata().toMap());
			result.put("location", locationInvariant.getLocation().toMap());
			result.put(entry.getName(), locationInvariant.getInvariant().toMap());
			return result;
		}
		throw new UnsupportedOperationException("Unknown entry type " + entry.getName());
	}
}
