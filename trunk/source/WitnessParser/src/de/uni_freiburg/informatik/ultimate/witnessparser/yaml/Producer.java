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

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 */
public class Producer {
	private final String mName;
	private final String mVersion;
	private final String mConfiguration;
	private final String mDescription;
	private final String mCommandLine;

	public Producer(final String name, final String version) {
		this(name, version, null, null, null);
	}

	public Producer(final String name, final String version, final String configuration, final String description,
			final String commandLine) {
		mName = name;
		mVersion = version;
		mConfiguration = configuration;
		mDescription = description;
		mCommandLine = commandLine;
	}

	public String getName() {
		return mName;
	}

	public String getVersion() {
		return mVersion;
	}

	public String getConfiguration() {
		return mConfiguration;
	}

	public String getDescription() {
		return mDescription;
	}

	public String getCommandLine() {
		return mCommandLine;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}

		if (obj instanceof Producer) {
			final Producer other = Producer.class.cast(obj);
			// @formatter:off
			if (getName().equals(other.getName()) &&
				getVersion().equals(other.getVersion()) &&
				getConfiguration().equals(other.getConfiguration()) &&
				getDescription().equals(other.getDescription()) &&
				getCommandLine().equals(other.getCommandLine())) {

				return true;
			}
			// @formatter:on
		}

		return false;
	}

	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("name", mName);
		result.put("version", mVersion);
		return result;
	}
}
