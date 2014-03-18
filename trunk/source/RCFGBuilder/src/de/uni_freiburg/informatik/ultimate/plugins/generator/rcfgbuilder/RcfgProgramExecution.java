package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

public class RcfgProgramExecution implements IProgramExecution<RcfgElement, Expression> {

	private final List<CodeBlock> m_Trace;
	private final Map<Integer, ProgramState<Expression>> m_PartialProgramStateMapping;
	private final Map<TermVariable, Boolean>[] m_BranchEncoders;
	private final boolean m_Overapproximation;

	public RcfgProgramExecution(List<CodeBlock> trace,
			Map<Integer, ProgramState<Expression>> partialProgramStateMapping,
			Map<TermVariable, Boolean>[] branchEncoders) {
		super();
		assert trace != null;
		assert partialProgramStateMapping != null;
		assert branchEncoders != null;
		m_Trace = trace;
		m_PartialProgramStateMapping = partialProgramStateMapping;
		m_BranchEncoders = branchEncoders;
		m_Overapproximation = containsOverapproximationFlag(trace);
	}

	/**
	 * Returns true if this trace is an overapproximation of the original trace.
	 */
	public boolean isOverapproximation() {
		return m_Overapproximation;
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
		if (i < 0 || i >= m_Trace.size()) {
			throw new IllegalArgumentException("out of range");
		}
		return m_PartialProgramStateMapping.get(i);
	}

	@Override
	public ProgramState<Expression> getInitialProgramState() {
		return m_PartialProgramStateMapping.get(-1);
	}

	private boolean containsOverapproximationFlag(List<CodeBlock> trace) {
		for (CodeBlock cb : trace) {
			if (cb.getPayload().hasAnnotation()) {
				HashMap<String, IAnnotations> annotations = cb.getPayload().getAnnotations();
				if (annotations.containsKey(Overapprox.getIdentifier())) {
					return true;
				}
			}
		}
		return false;
	}

	private String ppstoString(ProgramState<Expression> pps) {
		String result;
		if (pps == null) {
			result = null;
		} else {
			StringBuilder sb = new StringBuilder();
			for (Expression variable : pps.getVariables()) {
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
		String valuation = ppstoString(getInitialProgramState());
		String lineSeparator = System.getProperty("line.separator");

		sb.append("=== Start of program execution");
		if (valuation != null) {
			sb.append("initial values:");
			sb.append(valuation);
			sb.append(lineSeparator);
		}
		for (int i = 0; i < m_Trace.size(); i++) {
			sb.append("statement");
			sb.append(i);
			sb.append(": ");
			sb.append(m_Trace.get(i).toString());
			sb.append(lineSeparator);
			valuation = ppstoString(getProgramState(i));
			if (valuation != null) {
				sb.append("values");
				sb.append(i);
				sb.append(":");
				sb.append(valuation);
				sb.append(lineSeparator);
			}
		}
		sb.append("=== End of program execution");
		return sb.toString();
	}

	/**
	 * Workaround to satisfy the parameters of results.
	 * 
	 * @return
	 */
	@Deprecated
	public List<ILocation> getLocationList() {
		List<ILocation> result = new ArrayList<ILocation>();
		for (CodeBlock cb : m_Trace) {
			result.add(cb.getPayload().getLocation());
		}
		return result;
	}

}
