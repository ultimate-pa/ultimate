/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ExceptionHandlingCategory;

/**
 * Provides reasons why the trace feasiblity result of {@link TraceCheck}
 * is unknown. 
 * Objects of this class will NOT provide reasons for failed interpolations. 
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class TraceCheckReasonUnknown {
	
	public enum Reason {
		/**
		 * Solver response was 'unknown' because of timeout.
		 * Often we are not able to detect the reason and hence timeouts
		 * are often classified as SOLVER_RESPONSE_OTHER.
		 */
		SOLVER_RESPONSE_TIMEOUT,

		/**
		 * Solver response to check-sat was unknown.
		 * This sometimes includes timeouts
		 */
		SOLVER_RESPONSE_OTHER,
		
		/**
		 * An Ultimate defined timeout was reached this can happen during
		 * the pre-processing (e.g., computing the SSA) or if statements
		 * are asserted incrementally and one trace check involves
		 * several check-sats 
		 */
		ULTIMATE_TIMEOUT,
		
		/**
		 * Formulas in trace use nonlinear arithmetic, but solver
		 * does not support non-linear arithmetic.
		 */
		UNSUPPORTED_NON_LINEAR_ARITHMETIC,
		
		/**
		 * Solver crash because an Ultimate developer used wrong parameters
		 */
		SOLVER_CRASH_WRONG_USAGE,
		
		/**
		 * Solver crash that does not fall in one of the other categories
		 */
		SOLVER_CRASH_OTHER,
		
		/**
		 * Solver crash because Ultimate developers do not follow SMT-LIB
		 * standard. E.g., according to SMT-LIB bvadd may only take 2
		 * parameters.
		 */
		ULTIMATE_VIOLATES_SMT_LIB_STANDARD_AND_SOLVER_COMPLAINS,
	}
	
	private final Reason mReason;
	private final Exception mException;
	private final ExceptionHandlingCategory mExceptionHandlingCategory;
	
	public TraceCheckReasonUnknown(final Reason reason, final Exception exception, final ExceptionHandlingCategory category) {
		super();
		mReason = reason;
		mException = exception;
		mExceptionHandlingCategory = category;
	}

	public Reason getReason() {
		return mReason;
	}

	public Exception getException() {
		return mException;
	}

	public ExceptionHandlingCategory getExceptionHandlingCategory() {
		return mExceptionHandlingCategory;
	}
	
	

}
