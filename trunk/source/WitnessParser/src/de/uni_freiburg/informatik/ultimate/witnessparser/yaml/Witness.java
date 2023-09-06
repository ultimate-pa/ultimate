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

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;
import com.amihaiemil.eoyaml.YamlSequenceBuilder;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;

/**
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 */
public class Witness extends BasePayloadContainer implements IYamlProvider {
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

	@Override
	public YamlNode toYaml() {
		final YamlSequenceBuilder builder = Yaml.createMutableYamlSequenceBuilder();
		mEntries.forEach(x -> builder.add(x.toYaml()));
		return builder.build();
	}

	public String toYamlString() {
		return toYaml().toString() + "\n";
	}

	public boolean isCorrectnessWitness() {
		// TODO: Check this, when we also support violation witnesses
		return true;
	}
}
