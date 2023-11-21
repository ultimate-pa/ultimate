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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.management.RuntimeErrorException;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;

/**
*
* This class contains all conditions to be verified for the property check state-recoverability.
*
* @author Tobias Wießner <tobias.wiessner@mailbox.org>
*
*/

public class StateRecoverabilityVerificationConditionContainer {

	// Pattern for input expression
	public static final String exprPattern = "\\s{0,1}((\\w+)\\s*([<>=!][=]*)\\s*(\\w+))\\s{0,1}";

	private IReq2Pea mReq2pea;
	private Map<String, StateRecoverabilityVerificationCondition> mVerificationExpressions;
	private Map<String, String> mVariableDataTypeMap;

	public StateRecoverabilityVerificationConditionContainer(IReq2Pea req2pea) {
		mReq2pea = req2pea;
		mVerificationExpressions = new HashMap<>();
		getDataTypeFromReq2Pea(req2pea);
	}

	private void getDataTypeFromReq2Pea(IReq2Pea req2Pea) {
		Map<String, String> variableDataTypeMap = new HashMap<>();
		for (ReqPeas reqPeas : req2Pea.getReqPeas()) {
			List<Entry<CounterTrace, PhaseEventAutomata>> mReq = reqPeas.getCounterTrace2Pea();
			for (Entry<CounterTrace, PhaseEventAutomata> entry : mReq) {
				PhaseEventAutomata pea = entry.getValue();
				for (Map.Entry<String, String> entryVariableDataType : pea.getVariables().entrySet()) {
					// TODO anpassen abhängig davon was es noch für Datentypen gibt
					variableDataTypeMap.put(entryVariableDataType.getKey(), entryVariableDataType.getValue());
				}
			}
		}
		mVariableDataTypeMap = variableDataTypeMap;
	}

	public Map<String, StateRecoverabilityVerificationCondition> getVerificationExpressions() {
		return mVerificationExpressions;
	}

	public void addExpression(String inputExpr) {
		List<StateRecoverabilityVerificationCondition> veList = new ArrayList<>();
		int grpVariable = 2;
		int grpOperator = 3;
		int grpValue = 4;
		String[] exprArray = inputExpr.split(",");
		for (String expr : exprArray) {
			Matcher m = match(expr, exprPattern);
			if (m.find()) {
				String sVariable = m.group(grpVariable);
				String sOperator = m.group(grpOperator);
				String sValue = m.group(grpValue);
				String dataType = mVariableDataTypeMap.get(sVariable);
				if (dataType == null) {
					BoogieType boogieType =  mReq2pea.getSymboltable().getId2Type().get(sVariable);
					dataType = boogieType.toString();
					if(dataType == null) {
						throw new IllegalArgumentException(
								getClass().getName() + " could not find data type for " + sVariable);
					}
					
				}
				veList.add(new StateRecoverabilityVerificationCondition(new String[] { sVariable, sOperator, sValue }, dataType));
			}
		}
		addVerificationExpression(veList);
	}

	private void addVerificationExpression(List<StateRecoverabilityVerificationCondition> veList) {
		for (StateRecoverabilityVerificationCondition ve : veList) {
			addVerificationExpression(ve);
		}
	}

	private void addVerificationExpression(StateRecoverabilityVerificationCondition ve) {
		if (mVerificationExpressions == null) {
			mVerificationExpressions = new HashMap<>();
		}
		mVerificationExpressions.put(ve.getVariable(), ve);
	}

	private Matcher match(String s, String pattern) {
		Pattern p = Pattern.compile(pattern);
		Matcher m = p.matcher(s);
		return m;
	}
}
