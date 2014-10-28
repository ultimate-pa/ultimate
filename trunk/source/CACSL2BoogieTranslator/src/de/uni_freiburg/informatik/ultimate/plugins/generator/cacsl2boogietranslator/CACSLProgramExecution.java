package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IPointerType;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIdExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml.GraphMLConverter;
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
		String fillChar = " ";

		List<String> lineNumerColumn = getLineNumberColumn(mTrace);
		int lineNumberColumnLength = getMaxLength(lineNumerColumn) + 2;

		List<String> stepInfoColum = getStepInfoColum(mTrace);
		int stepInfoColumLength = getMaxLength(stepInfoColum) + 2;
		if (stepInfoColumLength < 6) {
			// because of IVAL+2
			stepInfoColumLength = 6;
		}

		if (valuation != null) {
			sb.append(fillWithChar(fillChar, lineNumberColumnLength));
			addFixedLength(sb, "IVAL", stepInfoColumLength, fillChar);
			sb.append(valuation);
			sb.append(lineSeparator);
		}

		for (int i = 0; i < mTrace.size(); i++) {
			AtomicTraceElement<CACSLLocation> currentATE = mTrace.get(i);
			CACSLLocation currentStep = currentATE.getStep();

			String lineNumber = lineNumerColumn.get(i);
			String stepInfo = stepInfoColum.get(i);

			addFixedLength(sb, lineNumber, lineNumberColumnLength, fillChar);
			addFixedLength(sb, stepInfo, stepInfoColumLength, fillChar);

			if (currentStep instanceof CLocation) {
				IASTNode currentStepNode = ((CLocation) currentStep).getNode();

				String str = getStringFromIASTNode(currentStepNode);

				if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE)) {
					sb.append("!(");
					sb.append(str);
					sb.append(")");
				} else {
					sb.append(str);
				}
			} else if (currentStep instanceof ACSLLocation) {
				// do something if its an acsl node
				ACSLNode currentStepNode = ((ACSLLocation) currentStep).getNode();
				sb.append(currentStepNode.toString());
			} else {
				throw new UnsupportedOperationException();
			}
			sb.append(lineSeparator);
			valuation = ppstoString(getProgramState(i));
			if (valuation != null) {
				sb.append(fillWithChar(fillChar, lineNumberColumnLength));
				addFixedLength(sb, "VAL", stepInfoColumLength, fillChar);
				sb.append(valuation);
				sb.append(lineSeparator);
			}
		}
		return sb.toString();
	}

	private String getStringFromIASTNode(IASTNode currentStepNode) {
		String str = currentStepNode.getRawSignature();
		if (currentStepNode instanceof CASTIdExpression) {
			CASTIdExpression id = (CASTIdExpression) currentStepNode;
			if (id.getExpressionType() instanceof IPointerType) {
				str = "\\read(" + getPointerStars((IPointerType) id.getExpressionType()) + str + ")";
			} else {
				str = "\\read(" + str + ")";
			}
		}
		return str;
	}

	private String getPointerStars(IPointerType type) {
		if (type.getType() instanceof IPointerType) {
			return "*" + getPointerStars((IPointerType) type.getType());
		} else {
			return "*";
		}
	}

	private void addFixedLength(StringBuilder sb, String actualString, int fillLength, String fillChar) {
		sb.append(actualString);
		sb.append(fillWithChar(fillChar, fillLength - actualString.length()));
	}

	private String fillWithChar(String string, int length) {
		if (length <= 0) {
			return "";
		}
		StringBuffer outputBuffer = new StringBuffer(length);
		for (int i = 0; i < length; i++) {
			outputBuffer.append(string);
		}
		return outputBuffer.toString();
	}

	private int getMaxLength(List<String> lineNumerColumn) {
		int max = 0;
		for (String s : lineNumerColumn) {
			int length = s.length();
			if (length > max) {
				max = length;
			}
		}
		return max;
	}

	private List<String> getStepInfoColum(List<AtomicTraceElement<CACSLLocation>> trace) {
		List<String> rtr = new ArrayList<>();
		for (AtomicTraceElement<CACSLLocation> elem : trace) {
			if (elem.hasStepInfo(StepInfo.NONE)) {
				rtr.add("");
			} else {
				String str = elem.getStepInfo().toString();
				rtr.add(str.substring(1, str.length() - 1));
			}
		}
		return rtr;
	}

	private List<String> getLineNumberColumn(ArrayList<AtomicTraceElement<CACSLLocation>> trace) {
		List<String> rtr = new ArrayList<>();
		for (AtomicTraceElement<CACSLLocation> elem : trace) {
			StringBuilder sb = new StringBuilder();
			sb.append("[L");
			int start = elem.getStep().getStartLine();
			int end = elem.getStep().getEndLine();
			if (start == end) {
				sb.append(start);
			} else {
				sb.append(start);
				sb.append("-L");
				sb.append(end);
			}
			sb.append("]");
			rtr.add(sb.toString());
		}
		return rtr;
	}

	private String ppstoString(ProgramState<IASTExpression> pps) {
		if (pps == null) {
			return null;
		}

		List<IASTExpression> keys = new ArrayList<>(pps.getVariables());
		Collections.sort(keys, new Comparator<IASTExpression>() {
			@Override
			public int compare(IASTExpression arg0, IASTExpression arg1) {
				return getStringFromIASTNode(arg0).compareToIgnoreCase(getStringFromIASTNode(arg1));
			}
		});

		StringBuilder sb = new StringBuilder();
		sb.append("[");
		int i = 0;
		for (IASTExpression variable : keys) {
			i++;
			String varName = getStringFromIASTNode(variable);
			Collection<IASTExpression> values = pps.getValues(variable);
			for (IASTExpression value : values) {
				sb.append(varName);
				sb.append("=");
				sb.append(getStringFromIASTNode(value));
				if (i < keys.size()) {
					sb.append(", ");
				}
			}
		}
		sb.append("]");
		return sb.toString();
	}

	@Override
	public String getSVCOMPWitnessString() {
		// TODO: This call is just so I can explore methods to create the SVCOMP
		// witness format
		GraphMLConverter converter = new GraphMLConverter(this);
		String converted = converter.makeGraphMLString();
		return converted;
	}

}
