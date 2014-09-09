package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.HashMap;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

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
		// use BoogieProgramExecution
		// TODO Auto-generated method stub
		return super.translateProgramExecution(programExecution);
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
