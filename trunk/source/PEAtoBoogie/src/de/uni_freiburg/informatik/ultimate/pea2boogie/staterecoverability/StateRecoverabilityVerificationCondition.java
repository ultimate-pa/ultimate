/*
 * Copyright (C) 2023 Tobias Wießner <tobias.wiessner@mailbox.org>
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import javax.management.RuntimeErrorException;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;

/**
 *
 * This class contains a condition to be verified for the property check state-recoverability. An object of this class
 * is created via each condition entered in the GUI.
 *
 * @author Tobias Wießner <tobias.wiessner@mailbox.org>
 *
 */

public class StateRecoverabilityVerificationCondition {
	private final String[] expr;
	private final String dataType;
	private final int iVariable = 0;
	private final int iOperator = 1;
	private final int iValue = 2;

	public StateRecoverabilityVerificationCondition(String[] expr, String dataType) {
		this.expr = expr;
		this.dataType = dataType;
	}

	public String[] getExpr() {
		return expr;
	}

	public String getVariable() {
		return expr[iVariable];
	}

	public String getOperator() {
		return expr[iOperator];
	}

	public String getValue() {
		return expr[iValue];
	}

	public String getDataType() {
		return dataType;
	}

	public boolean getBoolValue() {
		if (expr[iValue].equals(StateRecoverabilityVerificationConditionContainer.BOOL)) {
			return Boolean.getBoolean(expr[iValue]);
		}

		throw new RuntimeErrorException(null,
				getClass().getName() + " data type " + dataType + " is not correct for " + expr);
	}

	public int getIntegerValue() {
		if (expr[iValue].equals(StateRecoverabilityVerificationConditionContainer.INT)) {
			return Integer.getInteger(expr[iValue]);
		}

		throw new RuntimeErrorException(null,
				getClass().getName() + " data type " + dataType + " is not correct for " + expr);
	}

	public double getDoubleValue() {
		if (expr[iValue].equals(StateRecoverabilityVerificationConditionContainer.REAL)) {
			return Double.parseDouble(expr[iValue]);
		}

		throw new RuntimeErrorException(null,
				getClass().getName() + " data type " + dataType + " is not correct for " + expr);
	}

	public BoogiePrimitiveType getBoogiePrimitiveType() {
		switch (dataType) {
		case "bool":
			return BoogiePrimitiveType.TYPE_BOOL;
		case "int":
			return BoogiePrimitiveType.TYPE_INT;
		case "real":
			return BoogiePrimitiveType.TYPE_REAL;
		default:
			return BoogiePrimitiveType.TYPE_ERROR;
		}
	}
}
