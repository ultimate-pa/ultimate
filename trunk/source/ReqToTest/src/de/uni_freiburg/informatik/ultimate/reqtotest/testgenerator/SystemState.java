package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;

public class SystemState extends ProgramState<Expression> {
	
	private final double mTime;
	private final Map<String,  Collection<Expression>> mIdentToValues = new HashMap<>();

	public SystemState(Map<Expression, Collection<Expression>> variable2Values, double time) {
		super(variable2Values);
		mTime = time;
		for(Expression v : variable2Values.keySet()) {
			mIdentToValues.put(((IdentifierExpression)v).getIdentifier(), variable2Values.get(v));
		}
	}

	public String toOracleString() {
		StringBuilder sb = new StringBuilder();
		for(Expression e: getVariables()) {
				sb.append(formatAssignment(e, getValues(e)));
		}
		return sb.toString();
	}
	
	public Collection<Expression> getValues(String ident){
		return mIdentToValues.get(ident);
	}
	
	public double getTimeStep() {
		return mTime;
	}
	
	public String toString() {	
		Set<Expression> variables = getVariables();
		ArrayList<String> output = new ArrayList<String>();
		for(Expression e: variables) {
				output.add(String.format("| %-60s|", formatAssignment(e, getValues(e))));
		}	
		int i = 0;
		for(Expression e: variables) {
				if(i < output.size()) {
					output.set(i, output.get(i) + (String.format(" %-60s|", formatAssignment(e, getValues(e)))));
				} else {
					output.add(String.format("|%120s| %-60s|","", formatAssignment(e, getValues(e))));
				}
				i++;
		}
		for(; i < output.size(); i++) {
			output.set(i, output.get(i) + "                                                            |");
		}
		StringBuilder sb = new StringBuilder();
		sb.append("----| Step: t ");
		sb.append(Double.toString(mTime));
		sb.append("|-------------------------------------------------------------------------------------------");
		sb.append(System.getProperty("line.separator"));
		sb.append(String.join(System.getProperty("line.separator") , output));
		return  sb.toString();
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
