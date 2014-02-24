package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.boogie;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IValuation;

public class BoogieProgramExecution implements IProgramExecution<BoogieASTNode, Expression> {
	
	private final List<Statement> m_Trace;
	private final Map<Integer, ProgramState<Expression>> m_PartialProgramStateMapping;
	
	

	public BoogieProgramExecution(
			List<Statement> trace,
			Map<Integer, ProgramState<Expression>> partialProgramStateMapping) {
		super();
		m_Trace = trace;
		m_PartialProgramStateMapping = partialProgramStateMapping;
	}
	

	@Override
	public int getLength() {
		return m_Trace.size();
	}

	@Override
	public Statement getTraceElement(int i) {
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
			sb.append(BoogieStatementPrettyPrinter.print(m_Trace.get(i)));
			sb.append(System.getProperty("line.separator"));
			sb.append("values");
			sb.append(i);
			sb.append(":");
			sb.append(ppstoString(getProgramState(i)));
			sb.append(System.getProperty("line.separator"));
		}
		return sb.toString();
	}
	
	public IValuation getValuation() {
		return new IValuation() {
			@Override
			public Map<String, SimpleEntry<IType, List<String>>> getValuesForFailurePathIndex(
					int index) {
				ProgramState<Expression> ps = getProgramState(index);
				if (ps == null) {
					return getEmtpyProgramState();
				} else {
					return translateProgramState(ps);
				}
			}
			
			public Map<String, SimpleEntry<IType, List<String>>> getEmtpyProgramState() {
				return Collections.emptyMap();
			}
			
			public Map<String, SimpleEntry<IType, List<String>>> translateProgramState(ProgramState<Expression> ps) {
				Map<String, SimpleEntry<IType, List<String>>> result = new HashMap<String, SimpleEntry<IType, List<String>>>();
				for (Expression var : ps.getVariables()) {
					String varString = BoogieStatementPrettyPrinter.print(var);
					List<String> valuesString = exprSet2StringList(ps.getValues(var));
					result.put(varString, new SimpleEntry<IType, List<String>>(var.getType(), valuesString));
				}
				return result;
			}
			
			private List<String> exprSet2StringList(Collection<Expression> expressions) {
				List<String> result = new ArrayList<String>(expressions.size());
				for (Expression expr : expressions) {
					result.add(BoogieStatementPrettyPrinter.print(expr));
				}
				return result;
			}
		};
	}
	
	
	public class IValuationWrapper implements IValuation {

		@Override
		public Map<String, SimpleEntry<IType, List<String>>> getValuesForFailurePathIndex(
				int index) {
			ProgramState<Expression> ps = getProgramState(index);
			if (ps == null) {
				return getEmtpyProgramState();
			} else {
				return translateProgramState(ps);
			}
		}
		
		public Map<String, SimpleEntry<IType, List<String>>> getEmtpyProgramState() {
			return Collections.emptyMap();
		}
		
		public Map<String, SimpleEntry<IType, List<String>>> translateProgramState(ProgramState<Expression> ps) {
			Map<String, SimpleEntry<IType, List<String>>> result = new HashMap<String, SimpleEntry<IType, List<String>>>();
			for (Expression var : ps.getVariables()) {
				String varString = BoogieStatementPrettyPrinter.print(var);
				List<String> valuesString = exprSet2StringList(ps.getValues(var));
				result.put(varString, new SimpleEntry<IType, List<String>>(var.getType(), valuesString));
			}
			return result;
		}
		
		private List<String> exprSet2StringList(Collection<Expression> expressions) {
			List<String> result = new ArrayList<String>(expressions.size());
			for (Expression expr : expressions) {
				result.add(BoogieStatementPrettyPrinter.print(expr));
			}
			return result;
		}
		
	}
	

}
