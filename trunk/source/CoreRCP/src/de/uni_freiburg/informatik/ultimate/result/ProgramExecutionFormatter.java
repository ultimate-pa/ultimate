package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ProgramExecutionFormatter<TE, E> {

	private final IProgramExecutionStringProvider<TE, E> mStringProvider;

	public ProgramExecutionFormatter(IProgramExecutionStringProvider<TE, E> stringProvider) {
		mStringProvider = stringProvider;
	}

	public String formatProgramExecution(IProgramExecution<TE, E> execution) {
		StringBuilder sb = new StringBuilder();
		String valuation = getValuesAsString(execution.getInitialProgramState());
		String lineSeparator = CoreUtil.getPlatformLineSeparator();
		String fillChar = " ";

		List<String> lineNumerColumn = getLineNumberColumn(execution);
		int lineNumberColumnLength = getMaxLength(lineNumerColumn) + 2;

		List<String> stepInfoColum = getStepInfoColum(execution);
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

		for (int i = 0; i < execution.getLength(); i++) {
			String lineNumber = lineNumerColumn.get(i);
			String stepInfo = stepInfoColum.get(i);

			addFixedLength(sb, lineNumber, lineNumberColumnLength, fillChar);
			addFixedLength(sb, stepInfo, stepInfoColumLength, fillChar);
			AtomicTraceElement<TE> currentATE = execution.getTraceElement(i);
			appendStepAsString(sb, currentATE, false);

			sb.append(lineSeparator);
			valuation = getValuesAsString(execution.getProgramState(i));
			if (valuation != null) {
				sb.append(fillWithChar(fillChar, lineNumberColumnLength));
				addFixedLength(sb, "VAL", stepInfoColumLength, fillChar);
				sb.append(valuation);
				sb.append(lineSeparator);
			}
		}
		return sb.toString();
	}

	private void appendStepAsString(StringBuilder sb, AtomicTraceElement<TE> currentATE, boolean witness) {
		TE currentStep = currentATE.getStep();
		String str = mStringProvider.getStringFromStep(currentStep);

		boolean witnessMode = witness
				&& (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE) || currentATE
						.hasStepInfo(StepInfo.CONDITION_EVAL_TRUE));

		if (witnessMode) {
			sb.append("[");
		}

		if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE)) {
			sb.append("!(");
			sb.append(str);
			sb.append(")");
		} else {
			sb.append(str);
		}

		if (witnessMode) {
			sb.append("]");
		}
	}

	private String getValuesAsString(ProgramState<E> programState) {
		if (programState == null) {
			return null;
		}

		List<E> keys = new ArrayList<>(programState.getVariables());
		if (keys.size() == 0) {
			return null;
		}

		Collections.sort(keys, new Comparator<E>() {
			@Override
			public int compare(E arg0, E arg1) {
				return mStringProvider.getStringFromExpression(arg0).compareToIgnoreCase(
						mStringProvider.getStringFromExpression(arg1));
			}
		});

		StringBuilder sb = new StringBuilder();
		sb.append("[");
		int i = 0;
		for (E variable : keys) {
			i++;
			String varName = mStringProvider.getStringFromExpression(variable);
			Collection<E> values = programState.getValues(variable);
			for (E value : values) {
				sb.append(varName);
				sb.append("=");
				sb.append(mStringProvider.getStringFromExpression(value));
				if (i < keys.size()) {
					sb.append(", ");
				}
			}
		}
		sb.append("]");
		return sb.toString();
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

	private List<String> getStepInfoColum(IProgramExecution<TE, E> execution) {
		List<String> rtr = new ArrayList<>();
		for (int i = 0; i < execution.getLength(); ++i) {
			AtomicTraceElement<TE> elem = execution.getTraceElement(i);
			if (elem.hasStepInfo(StepInfo.NONE)) {
				rtr.add("");
			} else {
				String str = elem.getStepInfo().toString();
				rtr.add(str.substring(1, str.length() - 1));
			}
		}
		return rtr;
	}

	private List<String> getLineNumberColumn(IProgramExecution<TE, E> execution) {
		List<String> rtr = new ArrayList<>();
		for (int i = 0; i < execution.getLength(); ++i) {
			AtomicTraceElement<TE> elem = execution.getTraceElement(i);
			StringBuilder sb = new StringBuilder();
			int start = mStringProvider.getStartLineNumberFromStep(elem.getStep());
			int end = mStringProvider.getEndLineNumberFromStep(elem.getStep());

			if (start < 0) {
				// skip this line number
				sb.append("[?]");
			} else {
				sb.append("[L");
				if (start == end) {
					sb.append(start);
				} else {
					sb.append(start);
					sb.append("-L");
					sb.append(end);
				}
				sb.append("]");
			}
			rtr.add(sb.toString());
		}
		return rtr;
	}

	/**
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 * 
	 * @param <TE>
	 * @param <E>
	 */
	public interface IProgramExecutionStringProvider<TE, E> {

		int getStartLineNumberFromStep(TE step);

		int getEndLineNumberFromStep(TE step);

		String getStringFromStep(TE step);

		String getStringFromTraceElement(TE traceelement);

		String getStringFromExpression(E expression);
	}

}
