package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml;

import java.math.BigDecimal;

import org.eclipse.cdt.core.dom.ast.IASTExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSLProgramExecution;
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

	public boolean hasStep() {
		return mATE != null;
	}

	public boolean isNegated() {
		if (!hasStep()) {
			return false;
		}
		return mATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE);
	}

	public String getLineNumber() {
		if (!hasStep()) {
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

	public String getEnterFunction() {
		if (!hasStep()) {
			return null;
		}
		// if(mATE.hasStepInfo(StepInfo.PROC_CALL)){
		// CACSLLocation currentStep = mATE.getStep();
		// if (currentStep instanceof CLocation) {
		// IASTNode currentStepNode = ((CLocation) currentStep).getNode();
		// String str = currentStepNode.getRawSignature();
		// }
		// }
		return null;
	}

	public String getReturnFunction() {
		if (!hasStep()) {
			return null;
		}
		return null;
	}

	public String getSourceCode() {
		if (!hasStep()) {
			return null;
		}
		return CACSLProgramExecution.getStepAsWitnessString(mATE);
	}

	private void appendValidExpression(IASTExpression var, IASTExpression val, StringBuilder sb) {

		String varStr = var.getRawSignature();
		String valStr = val.getRawSignature();

		if(varStr.contains("\\") || varStr.contains("&")){
			//is something like read, old, etc. 
			return;
		}
		
		try {
			new BigDecimal(valStr);
		} catch (Exception ex) {
			//this is no valid number literal, maybe its true or false? 
			if(!valStr.equalsIgnoreCase("true") && !valStr.equalsIgnoreCase("false")){
				//nope, give up
				return;
			}
		}

		sb.append(varStr);
		sb.append("=");
		sb.append(valStr);
		sb.append(";");
	}

}
