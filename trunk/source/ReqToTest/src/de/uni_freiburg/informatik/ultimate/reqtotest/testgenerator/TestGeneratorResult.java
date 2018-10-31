package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class TestGeneratorResult implements IResult  {
	
	private final List<SystemState> mTestStates;
	
	public TestGeneratorResult (List<SystemState> testStates) {
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
		StringBuilder sb = new StringBuilder();
		sb.append("Test Vector:"+System.getProperty("line.separator"));
		for(ProgramState<Expression> s : mTestStates) {
			sb.append(s.toString() + System.getProperty("line.separator"));
		}
		return sb.toString();
	}
	
	public String toString() {
		return "Fount Test for oracle: " + mTestStates.get(mTestStates.size()-1).toOracleString() ;
	}
	
}
