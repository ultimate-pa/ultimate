package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;

public class TestGeneratorResult implements IResult  {
	
	private final List<ProgramState<Expression>> mTestStates;
	
	public TestGeneratorResult (List<ProgramState<Expression>> testStates) {
		mTestStates = testStates;
	}

	@Override
	public String getPlugin() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getShortDescription() {
		// TODO Auto-generated method stub
		return toString();
	}

	@Override
	public String getLongDescription() {
		// TODO Auto-generated method stub
		return toString();
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("---------------------------------------------------------------------\n");
		for(ProgramState<Expression> s : mTestStates) {
			sb.append(s.toString() + "\n");
		}
		return sb.toString();
	}

}
