package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.management.RuntimeErrorException;

import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;

public class VerificationExpressionContainer {

	// Pattern for input expression
	public static final String exprPattern = "\\s{0,1}((\\w+)\\s*([<>=!][=]*)\\s*(\\w+))\\s{0,1}";

	// Data types
	public static final String BOOL = "bool";
	public static final String INT = "int";
	public static final String REAL = "real";

	private IReq2Pea mReq2pea;
	private Map<String, VerificationExpression> mVerificationExpressions;
	private Map<String, String> mVariableDataTypeMap;

	public VerificationExpressionContainer(IReq2Pea req2pea) {
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

	public Map<String, VerificationExpression> getVerificationExpressions() {
		return mVerificationExpressions;
	}

	public void addExpression(String inputExpr) {
		List<VerificationExpression> veList = new ArrayList<>();
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
					throw new IllegalArgumentException(
							getClass().getName() + " could not find data type for " + sVariable);
				}
				veList.add(new VerificationExpression(new String[] { sVariable, sOperator, sValue }, dataType));
			}
		}
		addVerificationExpression(veList);
	}

	private void addVerificationExpression(List<VerificationExpression> veList) {
		for (VerificationExpression ve : veList) {
			addVerificationExpression(ve);
		}
	}

	private void addVerificationExpression(VerificationExpression ve) {
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
