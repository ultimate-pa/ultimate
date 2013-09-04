package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

public class RcfgProgramExecution implements IProgramExecution<CodeBlock, Expression> {
	
	private final List<CodeBlock> m_Trace;
	private final Map<Integer, ProgramState<Expression>> m_PartialProgramStateMapping;
	private final Map<TermVariable, Boolean>[] m_BranchEncoders;
	
	

	public RcfgProgramExecution(
			List<CodeBlock> trace,
			Map<Integer, ProgramState<Expression>> partialProgramStateMapping,
			Map<TermVariable, Boolean>[] branchEncoders) {
		super();
		m_Trace = trace;
		m_PartialProgramStateMapping = partialProgramStateMapping;
		m_BranchEncoders = branchEncoders;
	}
	

	public Map<TermVariable, Boolean>[] getBranchEncoders() {
		return m_BranchEncoders;
	}

	@Override
	public int getLength() {
		return m_Trace.size();
	}

	@Override
	public CodeBlock getTraceElement(int i) {
		return m_Trace.get(i);
	}

	@Override
	public ProgramState<Expression> getProgramState(int i) {
		if (i<0  || i>=m_Trace.size()) {
			throw new IllegalArgumentException("out of range");
		}
		return m_PartialProgramStateMapping.get(i);
	}

	@Override
	public ProgramState<Expression> getInitialProgramState() {
		return m_PartialProgramStateMapping.get(-1);
	}
	
	private String ppstoString(ProgramState<Expression> pps) {
		String result;
		if (pps == null) {
			result = " not available";
		} else {
			StringBuilder sb = new StringBuilder();
			for (Expression variable  : pps.getVariables()) {
				Expression value = pps.getValues(variable).iterator().next();
				sb.append("  ");
				String var = BoogieStatementPrettyPrinter.print(variable);
				String val = BoogieStatementPrettyPrinter.print(value);
				sb.append(var + "=" + val);
			}
			result = sb.toString();
		}
		return result;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("initial values:");
		sb.append(ppstoString(getInitialProgramState()));
		sb.append(System.getProperty("line.separator"));
		for (int i=0; i<m_Trace.size(); i++) {
			sb.append("statement");
			sb.append(i);
			sb.append(": ");
			sb.append(m_Trace.get(i).toString());
			sb.append(System.getProperty("line.separator"));
			sb.append("values");
			sb.append(i);
			sb.append(":");
			sb.append(ppstoString(getProgramState(i)));
			sb.append(System.getProperty("line.separator"));
		}
		return sb.toString();
	}

}
