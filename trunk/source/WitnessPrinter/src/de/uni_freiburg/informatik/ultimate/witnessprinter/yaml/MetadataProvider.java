/*
 * Copyright (C) 2023 Manuel Bentele (bentele@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023-2024 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.witnessprinter.yaml;

import java.time.OffsetDateTime;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.UUID;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;

/**
 * Provides metadata to be used by different {@link YamlWitnessWriter}s.
 *
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MetadataProvider {

	private final FormatVersion mFormatVersion;
	private final String mProducer;
	private final String mProducerVersion;
	private final Map<String, String> mProgramHashes;
	private final String mSpecification;
	private final String mDataModel;
	private final String mLanguage;

	public MetadataProvider(final FormatVersion formatVersion, final String producer, final String producerVersion,
			final Map<String, String> programHashes, final String specification, final String architecture,
			final String language) {
		mFormatVersion = formatVersion;
		mProducer = producer;
		mProducerVersion = producerVersion;
		mProgramHashes = programHashes;
		mSpecification = specification;
		mDataModel = getDataModel(architecture);
		mLanguage = language;
	}

	private static String getDataModel(final String architecture) {
		if (architecture.contains("32")) {
			return "ILP32";
		}
		if (architecture.contains("64")) {
			return "LP64";
		}
		// Fallback, in case we don't set the architecture (UNUSED)
		return architecture;
	}

	/**
	 * Returns a map with fresh metadata, i.e. with a fresh UUID and the current timestamp.
	 */
	public Map<String, Object> getFreshMetadata() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("format_version", mFormatVersion.toString());
		result.put("uuid", UUID.randomUUID().toString());
		result.put("creation_time", OffsetDateTime.now().truncatedTo(ChronoUnit.SECONDS).toString());
		final LinkedHashMap<String, Object> producer = new LinkedHashMap<>();
		producer.put("name", mProducer);
		producer.put("version", mProducerVersion);
		result.put("producer", producer);
		final LinkedHashMap<String, Object> task = new LinkedHashMap<>();
		task.put("input_files", new ArrayList<>(mProgramHashes.keySet()));
		task.put("input_file_hashes", new HashMap<>(mProgramHashes));
		task.put("specification", mSpecification);
		task.put("data_model", mDataModel);
		task.put("language", mLanguage);
		result.put("task", task);
		return result;
	}
}
