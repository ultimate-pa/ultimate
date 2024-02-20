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
import java.util.Map;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class GhostVariable extends WitnessEntry {
	public static final String NAME = "ghost_variable";

	private final String mVariable;
	private final String mInitial;
	private final String mScope;
	private final String mType;

	public GhostVariable(final Metadata metadata, final String variable, final String initial, final String scope,
			final String type) {
		super(NAME, metadata);
		mVariable = variable;
		mInitial = initial;
		mScope = scope;
		mType = type;
	}

	public String getVariable() {
		return mVariable;
	}

	public String getInitial() {
		return mInitial;
	}

	public String getScope() {
		return mScope;
	}

	public String getType() {
		return mType;
	}

	@Override
	public WitnessSetEntry toSetEntry() {
		return new WitnessSetEntry(NAME, null,
				Map.of("variable", mVariable, "scope", mScope, "initial", mInitial, "c_type", mType));
	}

	@Override
	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("entry_type", NAME);
		result.put("metadata", mMetadata.toMap());
		result.put("variable", mVariable);
		result.put("scope", mScope);
		result.put("initial", mInitial);
		result.put("type", mType);
		return result;
	}
}
