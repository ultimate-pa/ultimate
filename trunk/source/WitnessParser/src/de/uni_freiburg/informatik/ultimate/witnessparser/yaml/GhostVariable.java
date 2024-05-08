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
 * This witness entry declares a ghost variable. The declaration is similar to a declaration in C, it consists of a
 * variable name, a type and a initial value. The scope determines the location of this initialization.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class GhostVariable extends WitnessEntry {
	public static final String NAME = "ghost_variable";

	private final String mVariable;
	private final String mInitialValue;
	private final String mValueFormat;
	private final String mScope;
	private final String mType;

	public GhostVariable(final String variable, final String initialValue, final String valueFormat, final String scope,
			final String type) {
		super(NAME);
		mVariable = variable;
		mInitialValue = initialValue;
		mScope = scope;
		mType = type;
		mValueFormat = valueFormat;
	}

	public String getVariable() {
		return mVariable;
	}

	public String getInitialValue() {
		return mInitialValue;
	}

	public String getScope() {
		return mScope;
	}

	public String getType() {
		return mType;
	}

	public String getValueFormat() {
		return mValueFormat;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName() + " " + mType + " " + mVariable + "=" + mInitialValue;
	}
}
