/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
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
import java.util.List;
import java.util.Map;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class FunctionContract extends WitnessEntry {

	/**
	 * Witness entry name of the YAML witness format.
	 */
	public static final String NAME = "function_contract";

	private final Location mLocation;
	private final String mFormat;
	// TODO: Add support for other elements of the contracts
	private final List<String> mRequires;
	private final List<String> mEnsures;

	public FunctionContract(final Metadata metadata, final Location location, final List<String> requires,
			final List<String> ensures, final String format) {
		super(NAME, metadata);
		mLocation = location;
		mFormat = format;
		mRequires = requires == null ? List.of() : requires;
		mEnsures = ensures == null ? List.of() : ensures;
	}

	public Location getLocation() {
		return mLocation;
	}

	public List<String> getRequires() {
		return mRequires;
	}

	public List<String> getEnsures() {
		return mEnsures;
	}

	@Override
	public WitnessSetEntry toSetEntry() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		if (!mRequires.isEmpty()) {
			result.put("requires", mRequires);
		}
		if (!mEnsures.isEmpty()) {
			result.put("ensures", mEnsures);
		}
		result.put("format", mFormat);
		return new WitnessSetEntry(NAME, mLocation, result);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName() + " " + mLocation + ": " + mEnsures;
	}

	@Override
	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("entry_type", NAME);
		result.put("metadata", mMetadata.toMap());
		result.put("location", mLocation.toMap());
		if (!mRequires.isEmpty()) {
			result.put("requires", mRequires);
		}
		if (!mEnsures.isEmpty()) {
			result.put("ensures", mEnsures);
		}
		result.put("format", mFormat);
		return result;
	}
}
