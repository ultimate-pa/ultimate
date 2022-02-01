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
package de.uni_freiburg.informatik.ultimate.core.lib.translation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class ProgramExecutionFormatter<TE, E> {

	private final IBacktranslationValueProvider<TE, E> mStringProvider;

	public ProgramExecutionFormatter(final IBacktranslationValueProvider<TE, E> stringProvider) {
		mStringProvider = stringProvider;
	}

	public String formatProgramExecution(final IProgramExecution<TE, E> execution) {
		final StringBuilder sb = new StringBuilder();
		String valuation = getValuesAsString(execution.getInitialProgramState());
		final String lineSeparator = CoreUtil.getPlatformLineSeparator();
		final String fillChar = " ";

		final List<String> lineNumerColumn = getLineNumberColumn(execution);
		final int lineNumberColumnLength = getColumnMaxLength(lineNumerColumn);

		final List<String> stepInfoColum = getStepInfoColum(execution);
		int stepInfoColumLength = getColumnMaxLength(stepInfoColum);
		if (stepInfoColumLength < 6) {
			// because of IVAL+2
			stepInfoColumLength = 6;
		}

		final List<String> threadIdColumn = getThreadIdColumn(execution);
		final int threadIdColumnLength = getColumnMaxLength(threadIdColumn);

		final List<String> relevanceInfoColum = getRelevanceInformationColumn(execution);
		final int relevanceInfoColumnLength = getColumnMaxLength(relevanceInfoColum);

		final int valOffset = stepInfoColumLength + relevanceInfoColumnLength + threadIdColumnLength;
		if (valuation != null) {
			sb.append(fillWithChar(fillChar, lineNumberColumnLength));
			addFixedLength(sb, "IVAL", valOffset, fillChar);
			sb.append(valuation);
			sb.append(lineSeparator);
		}

		for (int i = 0; i < execution.getLength(); i++) {
			addFixedLength(sb, lineNumerColumn, i, lineNumberColumnLength, fillChar);
			addFixedLength(sb, stepInfoColum, i, stepInfoColumLength, fillChar);
			addFixedLength(sb, relevanceInfoColum, i, relevanceInfoColumnLength, fillChar);
			addFixedLength(sb, threadIdColumn, i, threadIdColumnLength, fillChar);

			final AtomicTraceElement<TE> currentATE = execution.getTraceElement(i);
			appendStepAsString(sb, currentATE, false);

			sb.append(lineSeparator);
			valuation = getValuesAsString(execution.getProgramState(i));
			if (valuation != null) {
				sb.append(fillWithChar(fillChar, lineNumberColumnLength));
				addFixedLength(sb, "VAL", valOffset, fillChar);
				sb.append(valuation);
				sb.append(lineSeparator);
			}
		}
		return sb.toString();
	}

	private void appendStepAsString(final StringBuilder sb, final AtomicTraceElement<TE> currentATE,
			final boolean witness) {
		final TE currentStep = currentATE.getStep();
		final String str = mStringProvider.getStringFromStep(currentStep);

		final boolean witnessMode = witness && (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE)
				|| currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_TRUE));

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

	private String getValuesAsString(final ProgramState<E> programState) {
		if (programState == null) {
			return null;
		}

		final List<E> keys = new ArrayList<>(programState.getVariables());
		if (keys.isEmpty()) {
			return null;
		}

		Collections.sort(keys, (arg0, arg1) -> mStringProvider.getStringFromExpression(arg0)
				.compareToIgnoreCase(mStringProvider.getStringFromExpression(arg1)));

		final StringBuilder sb = new StringBuilder();
		sb.append("[");
		int i = 0;
		for (final E variable : keys) {
			i++;
			final String varName = mStringProvider.getStringFromExpression(variable);
			final Collection<E> values = programState.getValues(variable);
			for (final E value : values) {
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

	private static void addFixedLength(final StringBuilder sb, final String actualString, final int fillLength,
			final String fillChar) {
		sb.append(actualString);
		sb.append(fillWithChar(fillChar, fillLength - actualString.length()));
	}

	private static void addFixedLength(final StringBuilder sb, final List<String> column, final int index,
			final int fillLength, final String fillChar) {
		if (column == null) {
			return;
		}
		addFixedLength(sb, column.get(index), fillLength, fillChar);
	}

	private static String fillWithChar(final String string, final int length) {
		if (length <= 0) {
			return "";
		}
		final StringBuilder outputBuffer = new StringBuilder(length);
		for (int i = 0; i < length; i++) {
			outputBuffer.append(string);
		}
		return outputBuffer.toString();
	}

	private static int getColumnMaxLength(final List<String> column) {
		if (column == null) {
			return 0;
		}
		return getMaxLength(column) + 2;
	}

	private static int getMaxLength(final List<String> lineNumerColumn) {
		int max = 0;
		for (final String s : lineNumerColumn) {
			final int length = s.length();
			if (length > max) {
				max = length;
			}
		}
		return max;
	}

	private List<String> getThreadIdColumn(final IProgramExecution<TE, E> execution) {
		if (!execution.isConcurrent()) {
			return null;
		}
		final List<String> rtr = new ArrayList<>();
		for (int i = 0; i < execution.getLength(); ++i) {
			final AtomicTraceElement<TE> elem = execution.getTraceElement(i);
			rtr.add(String.valueOf(elem.getThreadId()));
		}
		return rtr;
	}

	private List<String> getStepInfoColum(final IProgramExecution<TE, E> execution) {
		final List<String> rtr = new ArrayList<>();
		for (int i = 0; i < execution.getLength(); ++i) {
			final AtomicTraceElement<TE> elem = execution.getTraceElement(i);
			if (elem.hasStepInfo(StepInfo.NONE)) {
				rtr.add("");
			} else {
				final String str = elem.getStepInfo().toString();
				rtr.add(str.substring(1, str.length() - 1));
			}
		}
		return rtr;
	}

	private List<String> getLineNumberColumn(final IProgramExecution<TE, E> execution) {
		final List<String> rtr = new ArrayList<>();
		for (int i = 0; i < execution.getLength(); ++i) {
			final AtomicTraceElement<TE> elem = execution.getTraceElement(i);
			final StringBuilder sb = new StringBuilder();
			final int start = mStringProvider.getStartLineNumberFromStep(elem.getStep());
			final int end = mStringProvider.getEndLineNumberFromStep(elem.getStep());

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

	private List<String> getRelevanceInformationColumn(final IProgramExecution<TE, E> execution) {
		final List<String> rtr = new ArrayList<>();
		int numberOfRelevanceInformations = 0;
		for (int i = 0; i < execution.getLength(); ++i) {
			final IRelevanceInformation ri = execution.getTraceElement(i).getRelevanceInformation();
			if (ri == null) {
				rtr.add("?");
			} else {
				rtr.add(ri.getShortString());
				numberOfRelevanceInformations++;
			}
		}
		if (numberOfRelevanceInformations == 0) {
			return null;
		}
		return rtr;
	}

}
