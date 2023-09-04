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

/**
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 */

import java.util.List;
import java.util.Map;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;

public class Task implements IYamlProvider {
	private final List<String> mInputFiles;
	private final Map<String, String> mInputFileHashes;
	private final String mSpecification;
	private final String mDataModel;
	private final String mLanguage;

	public Task(final List<String> inputFiles, final Map<String, String> inputFileHashes, final String specification,
			final String dataModel, final String language) {
		mInputFiles = inputFiles;
		mInputFileHashes = inputFileHashes;
		mSpecification = specification;
		mDataModel = dataModel;
		mLanguage = language;
	}

	private static YamlNode fromList(final List<String> list) {
		final var builder = Yaml.createMutableYamlSequenceBuilder();
		list.forEach(builder::add);
		return builder.build();
	}

	private static YamlNode fromMap(final Map<String, String> map) {
		final var builder = Yaml.createMutableYamlMappingBuilder();
		map.forEach(builder::add);
		return builder.build();
	}

	@Override
	public YamlNode toYaml() {
		return Yaml.createYamlMappingBuilder().add("input_files", fromList(mInputFiles))
				.add("input_file_hashes", fromMap(mInputFileHashes)).add("specification", mSpecification)
				.add("data_model", mDataModel).add("language", mLanguage).build();
	}
}
