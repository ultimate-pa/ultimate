package de.uni_freiburg.informatik.ultimate.model.boogie;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IValuation;
import de.uni_freiburg.informatik.ultimate.result.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.result.ProgramExecutionFormatter.IProgramExecutionStringProvider;
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

	@Override
	public String toString() {
		ProgramExecutionFormatter<BoogieASTNode, Expression> pef = new ProgramExecutionFormatter<>(
				new BoogieProgramExecutionStringProvider());
		return pef.formatProgramExecution(this);
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

	/**
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 * 
	 */
	private class BoogieProgramExecutionStringProvider implements
			IProgramExecutionStringProvider<BoogieASTNode, Expression> {

		@Override
		public int getStartLineNumberFromStep(BoogieASTNode step) {
			if (step.getLocation() == null) {
				return -1;
			}
			return step.getLocation().getStartLine();
		}

		@Override
		public int getEndLineNumberFromStep(BoogieASTNode step) {
			if (step.getLocation() == null) {
				return -1;
			}
			return step.getLocation().getEndLine();
		}

		@Override
		public String getStringFromStep(BoogieASTNode step) {
			if (step instanceof Statement) {
				return BoogiePrettyPrinter.print((Statement) step);
			} else if (step instanceof Specification) {
				return BoogiePrettyPrinter.print((Specification) step);
			} else if (step instanceof Expression) {
				return BoogiePrettyPrinter.print((Expression) step);
			} else {
				throw new IllegalArgumentException("current step is neither Statement nor Specification nor Expression");
			}
		}

		@Override
		public String getStringFromTraceElement(BoogieASTNode traceelement) {
			return getStringFromStep(traceelement);
		}

		@Override
		public String getStringFromExpression(Expression expression) {
			return BoogiePrettyPrinter.print(expression);
		}

	}
}
