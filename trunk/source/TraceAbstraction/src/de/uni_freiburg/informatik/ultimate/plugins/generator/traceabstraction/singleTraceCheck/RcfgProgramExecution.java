package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

public class RcfgProgramExecution implements IProgramExecution<CodeBlock, Expression> {
	
	private final List<CodeBlock> m_Trace;
	private final Map<Integer, PartialProgramState<Expression>> m_PartialProgramStateMapping;
	
	

	public RcfgProgramExecution(
			List<CodeBlock> trace,
			Map<Integer, PartialProgramState<Expression>> partialProgramStateMapping) {
		super();
		m_Trace = trace;
		m_PartialProgramStateMapping = partialProgramStateMapping;
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
	public PartialProgramState<Expression> getPartialProgramState(int i) {
		if (i<0  || i>=m_Trace.size()) {
			throw new IllegalArgumentException("out of range");
		}
		return m_PartialProgramStateMapping.get(i);
	}

	@Override
	public PartialProgramState<Expression> getInitialPartialProgramState() {
		return null;
	}
	
	private String ppstoString(PartialProgramState<Expression> pps) {
		String result;
		if (pps == null) {
			result = " unknown";
		} else {
			StringBuilder sb = new StringBuilder();
			for (Entry<Expression, Collection<Expression>> entry  : pps.getVariable2Values().entrySet()) {
				sb.append("  ");
				String var = BoogieStatementPrettyPrinter.print(entry.getKey());
				String val = BoogieStatementPrettyPrinter.print(entry.getValue().iterator().next());
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
		sb.append(ppstoString(getInitialPartialProgramState()));
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
			sb.append(ppstoString(getPartialProgramState(i)));
			sb.append(System.getProperty("line.separator"));
		}
		return sb.toString();
	}

}
