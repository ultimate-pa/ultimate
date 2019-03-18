package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class SystemState extends ProgramState<Expression> {
	
	private final int mTime;
	private final Map<String,  Collection<Expression>> mIdentToValues = new HashMap<>();

	public SystemState(Map<Expression, Collection<Expression>> variable2Values, int time) {
		super(variable2Values);
		mTime = time;
		for(Expression v : variable2Values.keySet()) {
			mIdentToValues.put(((IdentifierExpression)v).getIdentifier(), variable2Values.get(v));
		}
	}
	
	public Collection<Expression> getValues(String ident){
		return mIdentToValues.get(ident);
	}
	
	public int getTimeStep() {
		return mTime;
	}
	
	public String getVarSetToValueSet(Set<TermVariable> varSet) {
		StringBuilder sb = new StringBuilder();
		for(TermVariable var: varSet) {
			sb.append(String.format(var.getName()));
			sb.append(" := ");
			for(Expression expr: getValues(var.getName())){
				sb.append(BoogiePrettyPrinter.print(expr));
			}
			sb.append(", ");
		}
		return sb.toString();
	}
	
}
