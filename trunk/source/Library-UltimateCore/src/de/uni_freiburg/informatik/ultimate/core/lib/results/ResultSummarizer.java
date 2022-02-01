/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Evren Ermis
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AutomataScriptInterpreterOverallResult.OverallResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class ResultSummarizer {

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum ToolchainResult {
		NORESULT(-1), GENERICRESULT(0), CORRECT(1), UNPROVABLE(2), TIMEOUT(3), INCORRECT(4), SYNTAXERROR(5), ERROR(5);

		private int mValue;

		ToolchainResult(final int i) {
			mValue = i;
		}

		boolean isLess(final ToolchainResult other) {
			return mValue < other.mValue;
		}

		boolean isLessOrEqual(final ToolchainResult other) {
			return mValue <= other.mValue;
		}
	}

	private ToolchainResult mSummary;
	private String mDescription;

	public ResultSummarizer(final IResultService resultService) {
		processResults(resultService.getResults());
	}

	public ResultSummarizer(final Map<String, List<IResult>> results) {
		processResults(results);
	}

	private void processResults(final Map<String, List<IResult>> results) {
		ToolchainResult toolchainResult = ToolchainResult.NORESULT;
		String description = "Toolchain returned no result.";

		for (final List<IResult> PluginResults : results.values()) {
			for (final IResult result : PluginResults) {
				if (result instanceof SyntaxErrorResult) {
					toolchainResult = ToolchainResult.SYNTAXERROR;
					description = result.getShortDescription();
				} else if (result instanceof UnprovableResult) {
					if (toolchainResult.isLess(ToolchainResult.UNPROVABLE)) {
						toolchainResult = ToolchainResult.UNPROVABLE;
						description = "unable to determine feasibility of some traces";
					}
				} else if (result instanceof CounterExampleResult) {
					toolchainResult = updateIfLess(toolchainResult, ToolchainResult.INCORRECT);
				} else if (result instanceof PositiveResult) {
					toolchainResult = updateIfLess(toolchainResult, ToolchainResult.CORRECT);
				} else if (result instanceof ITimeoutResult) {
					if (toolchainResult.isLess(ToolchainResult.TIMEOUT)) {
						toolchainResult = ToolchainResult.TIMEOUT;
						description = "Timeout";
					}
				} else if (result instanceof GenericResultAtElement) {
					if (toolchainResult.isLessOrEqual(ToolchainResult.GENERICRESULT)) {
						toolchainResult = ToolchainResult.GENERICRESULT;
						description = result.getShortDescription() + "  " + result.getLongDescription();
					}
				} else if (result instanceof AutomataScriptInterpreterOverallResult) {
					final AutomataScriptInterpreterOverallResult autScriptInterpreterResult =
							(AutomataScriptInterpreterOverallResult) result;
					toolchainResult = translateAutomataScriptInterpreterOverallResult(
							autScriptInterpreterResult.getOverallResult());
					description = result.getLongDescription();
				} else if (result instanceof NonterminatingLassoResult) {
					toolchainResult = updateIfLess(toolchainResult, ToolchainResult.INCORRECT);
				} else if (result instanceof AllSpecificationsHoldResult) {
					toolchainResult = updateIfLess(toolchainResult, ToolchainResult.CORRECT);
				} else if (result instanceof TerminationArgumentResult<?, ?>) {
					toolchainResult = updateIfLess(toolchainResult, ToolchainResult.CORRECT);
				} else if (result instanceof ExceptionOrErrorResult) {
					toolchainResult = updateIfLess(toolchainResult, ToolchainResult.ERROR);
				} else if (result instanceof TerminationAnalysisResult) {
					final TerminationAnalysisResult tar = (TerminationAnalysisResult) result;
					switch (tar.getTermination()) {
					case NONTERMINATING:
						toolchainResult = updateIfLess(toolchainResult, ToolchainResult.INCORRECT);
						break;
					case TERMINATING:
						toolchainResult = updateIfLess(toolchainResult, ToolchainResult.CORRECT);
						break;
					case UNKNOWN:
					default:
						if (toolchainResult.isLess(ToolchainResult.UNPROVABLE)) {
							toolchainResult = ToolchainResult.UNPROVABLE;
							description = "unable to determine termination";
						}
						break;
					}
				}
			}
		}
		mSummary = toolchainResult;
		mDescription = description;
	}

	private static ToolchainResult updateIfLess(final ToolchainResult current, final ToolchainResult desired) {
		if (current.isLess(desired)) {
			return desired;
		}
		return current;
	}

	private static ToolchainResult translateAutomataScriptInterpreterOverallResult(final OverallResult overallResult) {
		switch (overallResult) {
		case ALL_ASSERTIONS_HOLD:
			return ToolchainResult.CORRECT;
		case SOME_ASSERTION_FAILED:
			return ToolchainResult.INCORRECT;
		case TIMEOUT:
			return ToolchainResult.TIMEOUT;
		case EXCEPTION_OR_ERROR:
		case NO_ASSERTION:
		case OUT_OF_MEMORY:
		default:
			return ToolchainResult.NORESULT;
		}
	}

	public ToolchainResult getResultSummary() {
		return mSummary;
	}

	public String getResultDescription() {
		return mDescription;
	}

	public String getOldResultMessage() {
		switch (getResultSummary()) {
		case SYNTAXERROR:
		case UNPROVABLE:
		case TIMEOUT:
		case NORESULT:
			return programUnknown(getResultDescription());
		case INCORRECT:
			return programIncorrect();
		case CORRECT:
			return programCorrect();
		case GENERICRESULT:
			return getResultDescription();
		default:
			throw new UnsupportedOperationException("unknown result " + getResultSummary());
		}
	}

	private static String programCorrect() {
		return "RESULT: Ultimate proved your program to be correct!";
	}

	private static String programIncorrect() {
		return "RESULT: Ultimate proved your program to be incorrect!";
	}

	private static String programUnknown(final String text) {
		return "RESULT: Ultimate could not prove your program: " + text;
	}
}
