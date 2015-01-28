package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ProductBacktranslator extends DefaultTranslator<CodeBlock, CodeBlock, Expression, Expression> {

	private final HashMap<RCFGEdge, RCFGEdge> mEdgeMapping;

	public ProductBacktranslator(Class<CodeBlock> traceElementType, Class<Expression> expressionType) {
		super(traceElementType, traceElementType, expressionType, expressionType);
		mEdgeMapping = new HashMap<>();
	}

	@SuppressWarnings("unchecked")
	@Override
	public IProgramExecution<CodeBlock, Expression> translateProgramExecution(
			IProgramExecution<CodeBlock, Expression> programExecution) {

		Map<TermVariable, Boolean>[] oldBranchEncoders = null;
		if (programExecution instanceof RcfgProgramExecution) {
			oldBranchEncoders = ((RcfgProgramExecution) programExecution).getBranchEncoders();
		}

		ArrayList<CodeBlock> newTrace = new ArrayList<>();
		Map<Integer, ProgramState<Expression>> newValues = new HashMap<>();
		ArrayList<Map<TermVariable, Boolean>> newBranchEncoders = new ArrayList<>();

		addProgramState(-1, newValues, programExecution.getInitialProgramState());

		for (int i = 0; i < programExecution.getLength(); ++i) {
			AtomicTraceElement<CodeBlock> currentATE = programExecution.getTraceElement(i);
			RCFGEdge mappedEdge = mEdgeMapping.get(currentATE.getTraceElement());
			if (mappedEdge == null || !(mappedEdge instanceof CodeBlock)) {
				// skip this, its not worth it.
				continue;
			}
			newTrace.add((CodeBlock) mappedEdge);
			addProgramState(i, newValues, programExecution.getProgramState(i));
			if (oldBranchEncoders != null) {
				newBranchEncoders.add(oldBranchEncoders[i]);
			}
		}

		return new RcfgProgramExecution(newTrace, newValues, newBranchEncoders.toArray(new Map[0]));
	}

	private void addProgramState(int i, Map<Integer, ProgramState<Expression>> newValues,
			ProgramState<Expression> programState) {
		newValues.put(i, programState);
	}

	@Override
	public List<CodeBlock> translateTrace(List<CodeBlock> trace) {
		return super.translateTrace(trace);
	}

	@Override
	public Expression translateExpression(Expression expression) {
		return super.translateExpression(expression);
	}

	public void mapEdges(RCFGEdge newEdge, RCFGEdge originalEdge) {
		RCFGEdge realOriginalEdge = mEdgeMapping.get(originalEdge);
		if (realOriginalEdge != null) {
			// this means we replaced an edge which we already replaced again
			// with something new, we have to map this to the real original
			mEdgeMapping.put(newEdge, realOriginalEdge);
		} else {
			mEdgeMapping.put(newEdge, originalEdge);
		}

	}

}
