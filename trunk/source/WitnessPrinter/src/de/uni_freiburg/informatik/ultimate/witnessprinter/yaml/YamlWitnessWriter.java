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

import java.util.List;
import java.util.Map;

import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;

/**
 * Abstract class to write a witness to YAML. Contains a method {@code formatYaml} that may be used to construct a
 * string.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public abstract class YamlWitnessWriter {
	/**
	 * Construct a writer for the matching {@code formatVersion}.
	 */
	public static YamlWitnessWriter construct(final FormatVersion formatVersion,
			final MetadataProvider metadataProvider) {
		if (formatVersion.getMajor() == 0) {
			return new YamlWitnessWriterV0(metadataProvider);
		}
		if (formatVersion.getMajor() == 2) {
			return new YamlWitnessWriterV2(metadataProvider, formatVersion.getMinor() >= 1);
		}
		throw new UnsupportedOperationException("Unknown format version " + formatVersion);
	}

	protected static String formatYaml(final List<Map<String, Object>> entries) {
		final DumperOptions options = new DumperOptions();
		options.setDefaultFlowStyle(DumperOptions.FlowStyle.BLOCK);
		options.setPrettyFlow(true);
		options.setSplitLines(false);
		options.setIndent(2);
		return new Yaml(options).dump(entries);
	}

	public abstract String toString(Witness witness);
}
