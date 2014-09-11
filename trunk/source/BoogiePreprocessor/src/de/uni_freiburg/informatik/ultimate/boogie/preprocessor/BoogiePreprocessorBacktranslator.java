package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;

public class BoogiePreprocessorBacktranslator extends
		DefaultTranslator<BoogieASTNode, BoogieASTNode, Expression, Expression> {

	private final Logger mLogger;
	/**
	 * Mapping from target nodes to source nodes (i.e. output to input)
	 */
	private final HashMap<BoogieASTNode, BoogieASTNode> mMapping;

	protected BoogiePreprocessorBacktranslator(Logger logger) {
		super(BoogieASTNode.class, BoogieASTNode.class, Expression.class, Expression.class);
		mLogger = logger;
		mMapping = new HashMap<>();
	}

	protected void addMapping(BoogieASTNode inputNode, BoogieASTNode outputNode) {
		BoogieASTNode realInputNode = mMapping.get(inputNode);
		if (realInputNode == null) {
			realInputNode = inputNode;
		}
		mMapping.put(outputNode, realInputNode);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Create mapping between");
			mLogger.debug("\tOutput " + printDebug(outputNode));
			mLogger.debug("\tInput  " + printDebug(realInputNode));
		}
	}

	private String printDebug(BoogieASTNode node) {
		if (node instanceof Statement) {
			return BoogieStatementPrettyPrinter.print((Statement) node);
		}

		if (node instanceof Expression) {
			return BoogieStatementPrettyPrinter.print((Expression) node);
		}

		if (node instanceof Procedure) {
			return BoogieStatementPrettyPrinter.printSignature((Procedure) node);
		}

		if (node instanceof VarList) {
			return BoogieStatementPrettyPrinter.print((VarList) node);
		}

		StringBuilder output = new StringBuilder();
		output.append(node.getClass().getSimpleName());
		ILocation loc = node.getLocation();

		if (loc != null) {
			int start = loc.getStartLine();
			int end = loc.getEndLine();

			output.append(" L");
			output.append(start);
			if (start != end) {
				output.append(":");
				output.append(end);
			}

			int startC = loc.getStartColumn();
			int endC = loc.getEndColumn();
			output.append(" C");
			output.append(startC);

			if (startC != endC) {
				output.append(":");
				output.append(endC);
			}
		}
		return output.toString();
	}

	@Override
	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> programExecution) {

		List<Statement> newTrace = new ArrayList<>();
		Map<Integer, ProgramState<Expression>> newPartialProgramStateMapping = new HashMap<>();

		int length = programExecution.getLength();
		for (int i = 0; i < length; ++i) {
			BoogieASTNode elem = programExecution.getTraceElement(i);
			BoogieASTNode newElem = mMapping.get(elem);

			if (newElem == null) {
				// do scary stuff
			} else {
				if (newElem instanceof Statement) {
					newTrace.add((Statement) newElem);
				} else {
					// do scary stuff
				}
			}

			// do stuff for the state
			ProgramState<Expression> state = programExecution.getProgramState(i);
			if (state == null) {
				newPartialProgramStateMapping.put(i, null);
			} else {
				Map<Expression, Collection<Expression>> newVariable2Values = new HashMap<>();

				// do smart stuff

				newPartialProgramStateMapping.put(i, new ProgramState<>(newVariable2Values));
			}
		}
		return super.translateProgramExecution(programExecution);
		// return new BoogieProgramExecution(newTrace,
		// newPartialProgramStateMapping);
	}

	@Override
	public List<BoogieASTNode> translateTrace(List<BoogieASTNode> trace) {
		// TODO Auto-generated method stub
		return super.translateTrace(trace);
	}

	@Override
	public Expression translateExpression(Expression expression) {
		// TODO Auto-generated method stub
		return super.translateExpression(expression);
	}

}
