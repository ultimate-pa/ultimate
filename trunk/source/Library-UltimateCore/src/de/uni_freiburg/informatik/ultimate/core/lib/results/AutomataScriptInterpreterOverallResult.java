/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity;

/**
 * While interpreting an automata script file such an overall result is constructed.
 *
 * @author Matthias Heizmann
 *
 */
public class AutomataScriptInterpreterOverallResult extends AbstractResult implements IResultWithSeverity {

	public enum OverallResult {
		ALL_ASSERTIONS_HOLD, NO_ASSERTION, SOME_ASSERTION_FAILED, EXCEPTION_OR_ERROR, TIMEOUT, OUT_OF_MEMORY
		// SYNTAX_ERROR
	}

	private final OverallResult mOverallResult;
	private final String mErrorMessage;

	public AutomataScriptInterpreterOverallResult(final String plugin, final OverallResult overallResult,
			final String errorMessage) {
		super(plugin);
		if (errorMessage == null && overallResult == OverallResult.EXCEPTION_OR_ERROR) {
			throw new UnsupportedOperationException("provide error message if there was an error");
		}
		if (errorMessage != null && overallResult != OverallResult.EXCEPTION_OR_ERROR
				&& overallResult != OverallResult.TIMEOUT) {
			throw new UnsupportedOperationException("provide error message only if there was an error or timeout");
		}
		mOverallResult = overallResult;
		mErrorMessage = errorMessage;
	}

	@Override
	public String getShortDescription() {
		switch (mOverallResult) {
		case ALL_ASSERTIONS_HOLD:
			return "Finished interpretation of automata script.";
		case EXCEPTION_OR_ERROR:
			return "Interpretation of automata script failed.";
		case NO_ASSERTION:
			return "Finished interpretation of automata script.";
		case SOME_ASSERTION_FAILED:
			return "Some assert statements have been evaluated to false.";
		// case SYNTAX_ERROR:
		case TIMEOUT:
			return "Timeout during interpretation of automata script.";
		case OUT_OF_MEMORY:
			return "Run out of memory during interpretation of automata script.";
		default:
			throw new AssertionError("unknown case");
		}
	}

	@Override
	public String getLongDescription() {
		switch (mOverallResult) {
		case ALL_ASSERTIONS_HOLD:
			return "All assert statements have been evaluated to true.";
		case NO_ASSERTION:
			return " You have not used any assert statement in your automata"
					+ " script. Assert statements can be used to check Boolean results.";
		default:
			return getShortDescription();
		}
	}

	@Override
	public Severity getSeverity() {
		switch (mOverallResult) {
		case ALL_ASSERTIONS_HOLD:
			return Severity.INFO;
		case EXCEPTION_OR_ERROR:
			return Severity.ERROR;
		case NO_ASSERTION:
			return Severity.INFO;
		case SOME_ASSERTION_FAILED:
			return Severity.ERROR;
		// case SYNTAX_ERROR:
		case TIMEOUT:
			return Severity.WARNING;
		case OUT_OF_MEMORY:
			return Severity.WARNING;
		default:
			throw new AssertionError("unknown case");
		}
	}

	public OverallResult getOverallResult() {
		return mOverallResult;
	}

	public String getErrorMessage() {
		if (mErrorMessage == null) {
			throw new UnsupportedOperationException("there is no error message, because there was no error");
		}
		return mErrorMessage;
	}

}
