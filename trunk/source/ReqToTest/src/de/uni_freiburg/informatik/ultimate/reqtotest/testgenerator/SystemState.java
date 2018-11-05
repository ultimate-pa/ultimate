package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;

public class SystemState extends ProgramState<Expression> {
	
	private final Set<Expression> mInputVariables;
	private final Map<Expression, Collection<Expression>> mReqLocations;
	private final double mTime;

	public SystemState(Map<Expression, Collection<Expression>> variable2Values, 
			Set<Expression> inputVariables, Map<Expression, Collection<Expression>> reqLocations, double time) {
		super(variable2Values);
		mInputVariables = inputVariables;
		mReqLocations = reqLocations;
		mTime = time;
	}
	
	public boolean isInput(Expression e) {
		return mInputVariables.contains(e);
	}

	public String toOracleString() {
		StringBuilder sb = new StringBuilder();
		for(Expression e: getVariables()) {
			if(!isInput(e)) {
				sb.append(formatAssignment(e, getValues(e)));
			}
		}
		return sb.toString();
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(Double.toString(mTime));
		sb.append( " | " );
		for(Expression e: getVariables()) {
			if(isInput(e)) {
				sb.append(formatAssignment(e, getValues(e)));
			}
		}		
		sb.append(" | ");
		for(Expression e: getVariables()) {
			if(!isInput(e)) {
				sb.append(formatAssignment(e, getValues(e)));
			}
		}
		sb.append("														 (");
		for(Expression e: mReqLocations.keySet()) {
			sb.append(formatAssignment(e, mReqLocations.get(e)));
		}
		sb.append(" ) ");
		return sb.toString();
	}
	
	private String formatAssignment(Expression e, Collection<Expression> values) {
		StringBuilder sb = new StringBuilder();
		sb.append( BoogiePrettyPrinter.print(e));
		sb.append( "=" );
		for(Expression value: values) {
			sb.append( BoogiePrettyPrinter.print(value));
		}
		sb.append("; ");
		return sb.toString();
	}
}
