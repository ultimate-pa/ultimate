/*
 * Copyright (C) 2023 Manuel Bentele (bentele@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.List;
import java.util.Map;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;

/**
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 */
public class Witness extends BasePayloadContainer {
	private static final long serialVersionUID = 2111530908758373549L;

	private final List<WitnessEntry> mEntries;

	public Witness(final List<WitnessEntry> entries) {
		mEntries = entries;
	}

	public List<WitnessEntry> getEntries() {
		return mEntries;
	}

	@Override
	public String toString() {
		return mEntries.toString();
	}

	public EntrySet toInvariantSet(final Supplier<Metadata> metadataSupplier) {
		return new EntrySet(metadataSupplier.get(),
				mEntries.stream().map(x -> x.toSetEntry()).collect(Collectors.toList()));
	}

	public String toYamlString() {
		final DumperOptions options = new DumperOptions();
		options.setDefaultFlowStyle(DumperOptions.FlowStyle.BLOCK);
		options.setPrettyFlow(true);
		options.setSplitLines(false);
		options.setIndent(2);
		return new Yaml(options).dump(mEntries.stream().map(WitnessEntry::toMap).collect(Collectors.toList()));
	}

	public boolean isCorrectnessWitness() {
		// TODO: Check this, when we also support violation witnesses
		return true;
	}

	/**
	 * Interface to transform data to a map for serialization.
	 *
	 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
	 */
	public interface IMapSerializable {
		Map<String, Object> toMap();
	}
}
