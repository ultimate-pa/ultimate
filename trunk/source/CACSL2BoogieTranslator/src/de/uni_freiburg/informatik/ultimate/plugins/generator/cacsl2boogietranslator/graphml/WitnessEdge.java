package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml;

import org.eclipse.cdt.core.dom.ast.IASTExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
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

	WitnessEdge(AtomicTraceElement<CACSLLocation> traceElement, long currentEdgeId) {
		mId = "E" + String.valueOf(currentEdgeId);
		mATE = traceElement;
		mState = null;
	}

	WitnessEdge(ProgramState<IASTExpression> state, long currentEdgeId) {
		mId = "E" + String.valueOf(currentEdgeId);
		mATE = null;
		mState = state;
	}

	public String getName() {
		return mId;
	}

	public boolean isAssumption() {
		return mState != null;
	}

	public boolean isNegated() {
		if (isAssumption()) {
			return false;
		}
		return mATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE);
	}

	public String getLineNumber() {
		if (isAssumption()) {
			return null;
		}
		return String.valueOf(mATE.getStep().getStartLine());
	}

	public String getSourceCode() {
		if (isAssumption()) {
			// TODO: Try this out
			// StringBuilder sb = new StringBuilder();
			// for(IASTExpression var : mState.getVariables()){
			// for(IASTExpression val : mState.getValues(var)){
			//
			// }
			// }
			return null;
		} else {
			CACSLLocation loc = mATE.getStep();
			if (loc instanceof CLocation) {
				CLocation cloc = (CLocation) loc;
				return cloc.getNode().getRawSignature();
			} else if (loc instanceof ACSLLocation) {

			}
			return null;
		}
	}

}
