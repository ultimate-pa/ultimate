package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml;

import org.eclipse.cdt.core.dom.ast.IASTExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.FakeExpression;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class WitnessEdge {

	private final String mId;
	private final AtomicTraceElement<CACSLLocation> mATE;
	private final ProgramState<IASTExpression> mState;

	WitnessEdge(AtomicTraceElement<CACSLLocation> traceElement, ProgramState<IASTExpression> state, long currentEdgeId) {
		mId = "E" + String.valueOf(currentEdgeId);
		mATE = traceElement;
		mState = state;
	}

	public boolean isDummy() {
		return mATE == null && mState == null;
	}

	public String getName() {
		return mId;
	}

	public boolean hasAssumption() {
		return mState != null;
	}

	public boolean isInitial() {
		return mState != null && mATE == null;
	}

	public boolean isNegated() {
		if (isDummy() || isInitial()) {
			return false;
		}
		return mATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE);
	}

	public String getLineNumber() {
		if (isDummy() || isInitial()) {
			return null;
		}
		return String.valueOf(mATE.getStep().getStartLine());
	}

	public String getAssumption() {
		if (!hasAssumption()) {
			return null;
		}

		StringBuilder sb = new StringBuilder();
		for (IASTExpression var : mState.getVariables()) {
			for (IASTExpression val : mState.getValues(var)) {
				appendValidExpression(var, val, sb);
			}
		}
		if (sb.length() > 0) {
			return sb.toString();
		}
		return null;
	}

	public String getSourceCode() {
		if (isDummy() || isInitial()) {
			return null;
		}

		CACSLLocation loc = mATE.getStep();
		if (loc instanceof CLocation) {
			CLocation cloc = (CLocation) loc;
			String rtr = cloc.getNode().getRawSignature();
			return rtr;
		} else if (loc instanceof ACSLLocation) {

		}
		return null;
	}

	private void appendValidExpression(IASTExpression var, IASTExpression val, StringBuilder sb) {
		if (var instanceof FakeExpression) {
			if (val instanceof FakeExpression) {
				sb.append(var.getRawSignature());
				sb.append("=");
				sb.append(val.getRawSignature());
				sb.append(";");
			}
		}
	}

}
