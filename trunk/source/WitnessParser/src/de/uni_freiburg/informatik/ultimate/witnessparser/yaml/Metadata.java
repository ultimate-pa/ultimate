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

import java.time.OffsetDateTime;
import java.time.temporal.ChronoUnit;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.UUID;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness.IMapSerializable;

/**
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 */
public class Metadata implements IMapSerializable {

	private final FormatVersion mFormatVersion;
	private final UUID mUuid;
	private final OffsetDateTime mCreationTime;
	private final Producer mProducer;
	private final Task mTask;

	public Metadata(final FormatVersion formatVersion, final UUID uuid, final OffsetDateTime creationTime,
			final Producer producer, final Task task) {
		mFormatVersion = formatVersion;
		mUuid = uuid;
		mCreationTime = creationTime;
		mProducer = producer;
		mTask = task;
	}

	public FormatVersion getFormatVersion() {
		return mFormatVersion;
	}

	public UUID getUuid() {
		return mUuid;
	}

	public OffsetDateTime getCreationTime() {
		return mCreationTime;
	}

	public Producer getProducer() {
		return mProducer;
	}

	public Task getTask() {
		return mTask;
	}

	@Override
	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("format_version", mFormatVersion.toString());
		result.put("uuid", mUuid.toString());
		result.put("creation_time", mCreationTime.truncatedTo(ChronoUnit.SECONDS).toString());
		result.put("producer", mProducer.toMap());
		result.put("task", mTask.toMap());
		return result;
	}
}
