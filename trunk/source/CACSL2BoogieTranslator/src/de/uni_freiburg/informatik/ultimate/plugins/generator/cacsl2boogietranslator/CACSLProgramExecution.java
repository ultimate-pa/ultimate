package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement.StepInfo;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class CACSLProgramExecution implements IProgramExecution<CACSLLocation, IASTExpression> {

	private final ProgramState<IASTExpression> mInitialState;
	private final ArrayList<ProgramState<IASTExpression>> mProgramStates;
	private final ArrayList<AtomicTraceElement<CACSLLocation>> mTrace;

	public CACSLProgramExecution(ProgramState<IASTExpression> initialState,
			Collection<AtomicTraceElement<CACSLLocation>> trace, Collection<ProgramState<IASTExpression>> programStates) {
		assert trace != null;
		assert programStates != null;
		assert trace.size() == programStates.size();
		mProgramStates = new ArrayList<>(programStates);
		mTrace = new ArrayList<>(trace);
		mInitialState = initialState;
	}

	@Override
	public int getLength() {
		return mTrace.size();
	}

	@Override
	public AtomicTraceElement<CACSLLocation> getTraceElement(int i) {
		return mTrace.get(i);
	}

	@Override
	public ProgramState<IASTExpression> getProgramState(int i) {
		return mProgramStates.get(i);
	}

	@Override
	public ProgramState<IASTExpression> getInitialProgramState() {
		return mInitialState;
	}

	@Override
	public Class<IASTExpression> getExpressionClass() {
		return IASTExpression.class;
	}

	@Override
	public Class<CACSLLocation> getTraceElementClass() {
		return CACSLLocation.class;
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
		for (int i = 0; i < mTrace.size(); i++) {
			AtomicTraceElement<CACSLLocation> currentATE = mTrace.get(i);
			CACSLLocation currentStep = currentATE.getStep();
			StepInfo currentStepInfo = currentATE.getStepInfo();

			sb.append("step");
			sb.append(i);
			sb.append(": ");

			if (currentStep.getCNode() != null && currentStep.getAcslNode() != null) {
				throw new UnsupportedOperationException("Mixed nodes are not yet supported");
			}

			if (currentStep.getCNode() != null) {
				IASTNode currentStepNode = currentStep.getCNode();
				switch (currentStepInfo) {
				case NONE:
				case CONDITION_EVAL_TRUE:
					sb.append(currentStepNode.getRawSignature());
					break;
				case CONDITION_EVAL_FALSE:
					// I couldnt build a printable CASTUnaryExpression, so I
					// just fake one..
					IASTExpression exp = (IASTExpression) currentStepNode;
					sb.append("!(");
					sb.append(exp.getRawSignature());
					sb.append(")");
					break;
				case CALL:
				case RETURN:
					sb.append(currentStepNode.getRawSignature());
					sb.append(" (");
					sb.append(currentStepInfo.toString());
					sb.append(")");
					break;
				default:
					throw new UnsupportedOperationException("Did not implement stepinfo " + currentStepInfo);
				}
			} else if (currentStep.getAcslNode() != null) {
				// do something if its an acsl node
				ACSLNode currentStepNode = currentStep.getAcslNode();
				sb.append(currentStepNode.toString());
			} else {
				throw new IllegalArgumentException("Step has no actual nodes!");
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

	private String ppstoString(ProgramState<IASTExpression> pps) {
		String result;
		if (pps == null) {
			result = null;
		} else {
			List<IASTExpression> keys = new ArrayList<>(pps.getVariables());
			Collections.sort(keys, new Comparator<IASTExpression>() {
				@Override
				public int compare(IASTExpression arg0, IASTExpression arg1) {
					return arg0.getRawSignature().compareToIgnoreCase(arg1.getRawSignature());
				}
			});

			StringBuilder sb = new StringBuilder();
			for (IASTExpression variable : keys) {
				IASTExpression value = pps.getValues(variable).iterator().next();
				sb.append("  ");
				String var = variable.getRawSignature();
				String val = value.getRawSignature();
				sb.append(var + "=" + val);
			}
			result = sb.toString();
		}
		return result;
	}

}
