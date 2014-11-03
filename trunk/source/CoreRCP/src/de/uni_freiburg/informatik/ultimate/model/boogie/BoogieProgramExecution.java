package de.uni_freiburg.informatik.ultimate.model.boogie;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.IValuation;
import de.uni_freiburg.informatik.ultimate.result.ResultUtil;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class BoogieProgramExecution implements IProgramExecution<BoogieASTNode, Expression> {

	private final List<AtomicTraceElement<BoogieASTNode>> m_Trace;
	private final Map<Integer, ProgramState<Expression>> m_PartialProgramStateMapping;

	/**
	 * Create a BoogieProgramExecution where every statement is an atomic step
	 * 
	 * @param trace
	 *            A trace consisting of atomic steps. May not be null and should
	 *            be immutable.
	 * @param partialProgramStateMapping
	 * 
	 */
	public BoogieProgramExecution(List<BoogieASTNode> trace,
			Map<Integer, ProgramState<Expression>> partialProgramStateMapping) {

		// a list of boogieastnodes is a trace that consists of atomic
		// statements.
		ArrayList<AtomicTraceElement<BoogieASTNode>> atomictrace = new ArrayList<>();
		for (BoogieASTNode te : trace) {
			atomictrace.add(new AtomicTraceElement<BoogieASTNode>(te));
		}

		m_Trace = atomictrace;
		m_PartialProgramStateMapping = partialProgramStateMapping;
	}

	public BoogieProgramExecution(Map<Integer, ProgramState<Expression>> partialProgramStateMapping,
			List<AtomicTraceElement<BoogieASTNode>> trace) {
		m_Trace = trace;
		m_PartialProgramStateMapping = partialProgramStateMapping;
	}

	@Override
	public int getLength() {
		return m_Trace.size();
	}

	@Override
	public AtomicTraceElement<BoogieASTNode> getTraceElement(int i) {
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

	private String ppstoString(ProgramState<Expression> pps) {
		if (pps == null) {
			return null;
		} else {
			List<Expression> keys = new ArrayList<>(pps.getVariables());
			Collections.sort(keys, new Comparator<Expression>() {
				@Override
				public int compare(Expression arg0, Expression arg1) {
					return BoogiePrettyPrinter.print(arg0).compareToIgnoreCase(BoogiePrettyPrinter.print(arg1));
				}
			});

			StringBuilder sb = new StringBuilder();
			for (Expression variable : keys) {
				Expression value = pps.getValues(variable).iterator().next();
				sb.append("  ");
				String var = BoogiePrettyPrinter.print(variable);
				String val = BoogiePrettyPrinter.print(value);
				sb.append(var + "=" + val);
			}
			if (sb.length() > 0) {
				return sb.toString();
			} else {
				return null;
			}
		}
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		String valuation = ppstoString(getInitialProgramState());
		String lineSeparator = System.getProperty("line.separator");
		if (valuation != null) {
			sb.append("initial values:");
			sb.append(valuation);
			sb.append(lineSeparator);
		}
		for (int i = 0; i < m_Trace.size(); i++) {
			AtomicTraceElement<BoogieASTNode> currentATE = m_Trace.get(i);
			BoogieASTNode currentStep = currentATE.getStep();

			sb.append("step");
			sb.append(i);
			sb.append(": ");

			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE)) {
				Expression exp = (Expression) currentStep;
				sb.append(BoogiePrettyPrinter.print(new UnaryExpression(exp.getLocation(),
						UnaryExpression.Operator.LOGICNEG, exp)));
			} else {
				if (currentStep instanceof Statement) {
					sb.append(BoogiePrettyPrinter.print((Statement) currentStep));
				} else if (currentStep instanceof Specification) {
					sb.append(BoogiePrettyPrinter.print((Specification) currentStep));
				} else if (currentStep instanceof Expression) {
					sb.append(BoogiePrettyPrinter.print((Expression) currentStep));
				} else {
					throw new IllegalArgumentException(
							"current step is neither Statement nor Specification nor Expression");
				}
			}
			if (!currentATE.hasStepInfo(StepInfo.NONE)) {
				sb.append(" ").append(currentATE.getStepInfo().toString());
			}

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
		return sb.toString();
	}

	public IValuation getValuation(final List<ITranslator<?, ?, ?, ?>> translatorSequence) {
		return new IValuation() {
			@Override
			public Map<String, SimpleEntry<IType, List<String>>> getValuesForFailurePathIndex(int index) {
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
					String varString = ResultUtil.backtranslationWorkaround(translatorSequence, var);
					List<String> valuesString = exprSet2StringList(ps.getValues(var));
					result.put(varString, new SimpleEntry<IType, List<String>>(var.getType(), valuesString));
				}
				return result;
			}

			private List<String> exprSet2StringList(Collection<Expression> expressions) {
				List<String> result = new ArrayList<String>(expressions.size());
				for (Expression expr : expressions) {
					result.add(ResultUtil.backtranslationWorkaround(translatorSequence, expr));
				}
				return result;
			}
		};
	}

	@Override
	public Class<Expression> getExpressionClass() {
		return Expression.class;
	}

	@Override
	public Class<BoogieASTNode> getTraceElementClass() {
		return BoogieASTNode.class;
	}

	@Override
	public String getSVCOMPWitnessString() {
		return null;
	}
}
