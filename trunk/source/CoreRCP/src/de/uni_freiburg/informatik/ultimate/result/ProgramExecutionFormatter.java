/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.model.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.result.model.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.model.IProgramExecution.ProgramState;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ProgramExecutionFormatter<TE, E> {

	private final IBacktranslationValueProvider<TE, E> mStringProvider;

	public ProgramExecutionFormatter(IBacktranslationValueProvider<TE, E> stringProvider) {
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
		
		final List<String> relevanceInfoColum = getRelevanceInformationColumn(execution);
		final int relevanceInfoColumnLength;
		if (relevanceInfoColum == null) {
			relevanceInfoColumnLength = 0;
		} else {
			relevanceInfoColumnLength = getMaxLength(relevanceInfoColum) + 2;
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
			if (relevanceInfoColum != null) {
				addFixedLength(sb, relevanceInfoColum.get(i), relevanceInfoColumnLength, fillChar);
			}
			AtomicTraceElement<TE> currentATE = execution.getTraceElement(i);
			appendStepAsString(sb, currentATE, false);

			sb.append(lineSeparator);
			valuation = getValuesAsString(execution.getProgramState(i));
			if (valuation != null) {
				sb.append(fillWithChar(fillChar, lineNumberColumnLength));
				addFixedLength(sb, "VAL", stepInfoColumLength + relevanceInfoColumnLength, fillChar);
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
	
	private List<String> getRelevanceInformationColumn(IProgramExecution<TE, E> execution) {
		List<String> rtr = new ArrayList<>();
		int numberOfRelevanceInformations = 0;
		for (int i = 0; i < execution.getLength(); ++i) {
			IRelevanceInformation ri = execution.getTraceElement(i).getmRelevanceInformation();
			if (ri == null) {
				rtr.add("?");
			} else {
				rtr.add(ri.getShortString());
				numberOfRelevanceInformations++;
			}
		}
		if (numberOfRelevanceInformations == 0) {
			return null;
		} else {
			return rtr;
		}
	}

}
