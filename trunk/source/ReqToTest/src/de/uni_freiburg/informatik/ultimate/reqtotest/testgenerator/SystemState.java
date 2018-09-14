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
	private final int mTime;

	public SystemState(Map<Expression, Collection<Expression>> variable2Values, Set<Expression> inputVariables, int time) {
		super(variable2Values);
		mInputVariables = inputVariables;
		mTime = time;
	}
	
	public boolean isInput(Expression e) {
		return mInputVariables.contains(e);
	}

	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(Integer.toString(mTime));
		sb.append( "| " );
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
		return sb.toString();
	}
	
	private String formatAssignment(Expression e, Collection<Expression> v) {
		StringBuilder sb = new StringBuilder();
		sb.append( BoogiePrettyPrinter.print(e));
		sb.append( "=" );
		for(Expression val : v) {
			sb.append( BoogiePrettyPrinter.print(val));
		}
		sb.append("; ");
		return sb.toString();
	}
}
