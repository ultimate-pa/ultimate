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

/**
 * This witness entry updates a ghost variable, i.e., assigns the given value to the variable with the given name. Only
 * ghost variables, where a corresponding {@link GhostVariable} exists in the witness, are allowed to be updated.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class GhostUpdate extends WitnessEntry {
	public static final String NAME = "ghost_update";

	private final String mVariable;
	private final String mValue;
	private final String mValueFormat;
	private final Location mLocation;

	public GhostUpdate(final String variable, final String value, final String valueFormat, final Location location) {
		super(NAME);
		mLocation = location;
		mVariable = variable;
		mValue = value;
		mValueFormat = valueFormat;
	}

	public String getVariable() {
		return mVariable;
	}

	public String getValue() {
		return mValue;
	}

	public Location getLocation() {
		return mLocation;
	}

	public String getValueFormat() {
		return mValueFormat;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName() + " " + mLocation + ": " + mVariable + " = " + mValue;
	}
}
