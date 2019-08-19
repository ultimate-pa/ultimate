/*
 * Copyright (C) 2016-2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2018 Christian Schilling (schilic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

/**
 * Provides reasons why the trace feasiblity result of {@link TraceCheck} is unknown. Objects of this class will NOT
 * provide reasons for failed interpolations.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class TraceCheckReasonUnknown {

	/**
	 * Reasons for {@link TraceCheckReasonUnknown}.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	public enum Reason {
		/**
		 * Solver response was 'unknown' because of timeout. Often we are not able to detect the reason and hence
		 * timeouts are often classified as SOLVER_RESPONSE_OTHER.
		 */
		SOLVER_RESPONSE_TIMEOUT,

		/**
		 * Solver response to check-sat was unknown. This sometimes includes timeouts
		 */
		SOLVER_RESPONSE_OTHER,

		/**
		 * An Ultimate defined timeout was reached this can happen during the pre-processing (e.g., computing the SSA)
		 * or if statements are asserted incrementally and one trace check involves several check-sats
		 */
		ULTIMATE_TIMEOUT,

		/**
		 * Formulas in trace use nonlinear arithmetic, but solver does not support non-linear arithmetic.
		 */
		UNSUPPORTED_NON_LINEAR_ARITHMETIC,

		/**
		 * Formulas in trace use const-arrays that are connected by a write chain
		 */
		UNSUPPORTED_CONST_ARRAY_WRITE_CHAINS,

		/**
		 * Formulas in trace contain quantifiers, but solver does not support quantifiers.
		 */
		UNSUPPORTED_QUANTIFIERS,

		/**
		 * Solver crash because an Ultimate developer used wrong parameters
		 */
		SOLVER_CRASH_WRONG_USAGE,

		/**
		 * Solver crash that does not fall in one of the other categories
		 */
		SOLVER_CRASH_OTHER,

		/**
		 * Solver crash because Ultimate developers do not follow SMT-LIB standard. E.g., according to SMT-LIB bvadd may
		 * only take 2 parameters.
		 */
		ULTIMATE_VIOLATES_SMT_LIB_STANDARD_AND_SOLVER_COMPLAINS,
	}

	/**
	 * Categories for exception handling.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum ExceptionHandlingCategory {
		/**
		 * The exception is known and we always want to ignore it.
		 */
		KNOWN_IGNORE,
		/**
		 * The exception is known and we sometimes want it to be thrown depending on the use case.
		 */
		KNOWN_DEPENDING,
		/**
		 * The exception is known and we always want it to be thrown.
		 */
		KNOWN_THROW,
		/**
		 * The exception is unknown and we usually want it to be thrown.
		 */
		UNKNOWN;

		/**
		 * @param throwSpecification
		 *            Specifies which exception categories should be thrown.
		 * @return {@code true} iff this exception category should be thrown.
		 */
		public boolean throwException(final RefinementStrategyExceptionBlacklist throwSpecification) {
			switch (throwSpecification) {
			case ALL:
				return true;
			case DEPENDING:
				return this == UNKNOWN || this == KNOWN_THROW || this == KNOWN_DEPENDING;
			case UNKNOWN:
				return this == UNKNOWN || this == KNOWN_THROW;
			case NONE:
				return false;
			default:
				throw new IllegalArgumentException("Unknown category specification: " + throwSpecification);
			}
		}
	}

	/**
	 * Specifies which categories of exceptions to throw. All other categories are ignored.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @see ExceptionHandlingCategory
	 */
	public enum RefinementStrategyExceptionBlacklist {
		/**
		 * Throw no exceptions.
		 */
		NONE,
		/**
		 * Throw only unknown exceptions.
		 */
		UNKNOWN,
		/**
		 * Throw unknown exceptions and known exceptions that are categorized as "sometimes good, sometimes bad".
		 */
		DEPENDING,
		/**
		 * Throw all exceptions.
		 */
		ALL
	}

	private static final String SMTINTERPOL_NONLINEAR_ARITHMETIC_MESSAGE = "Unsupported non-linear arithmetic";
	private static final String CVC4_NONLINEAR_ARITHMETIC_MESSAGE_PREFIX = "A non-linear fact";
	private static final String CVC4_CONST_ARRAY_WRITE_CHAIN_CONNECTION_MESSAGE =
			"Array theory solver does not yet support write-chains connecting two different constant arrays";

	private final Reason mReason;
	private final Exception mException;
	private final ExceptionHandlingCategory mExceptionHandlingCategory;

	public TraceCheckReasonUnknown(final Reason reason, final Exception exception,
			final ExceptionHandlingCategory category) {
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

	public static TraceCheckReasonUnknown constructReasonUnknown(final SMTLIBException e) {
		final String message = e.getMessage();
		final Reason reason;
		final ExceptionHandlingCategory exceptionCategory;
		if (message == null) {
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
		} else if (message.equals(SMTINTERPOL_NONLINEAR_ARITHMETIC_MESSAGE)) {
			// SMTInterpol does not support non-linear arithmetic
			reason = Reason.UNSUPPORTED_NON_LINEAR_ARITHMETIC;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.equals(CVC4_CONST_ARRAY_WRITE_CHAIN_CONNECTION_MESSAGE)) {
			// CVC4 crashes because two const-arrays are connected in a write chain
			reason = Reason.UNSUPPORTED_CONST_ARRAY_WRITE_CHAINS;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.startsWith("Cannot handle literal")) {
			// SMTInterpol cannot handle quantifiers
			reason = Reason.UNSUPPORTED_QUANTIFIERS;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_DEPENDING;
		} else if (message.startsWith(CVC4_NONLINEAR_ARITHMETIC_MESSAGE_PREFIX)) {
			// CVC4 does not support nonlinear arithmetic if some LIA or LRA logic is used.
			reason = Reason.UNSUPPORTED_NON_LINEAR_ARITHMETIC;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.endsWith("Connection to SMT solver broken")) {
			// broken SMT solver connection can have various reasons such as misconfiguration or solver crashes
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_DEPENDING;
		} else if (message.endsWith("Received EOF on stdin. No stderr output.")) {
			// problem with Z3
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_DEPENDING;
		} else if (message.contains("Received EOF on stdin. stderr output:")) {
			// problem with CVC4
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_THROW;
		} else if (message.startsWith("Logic does not allow numerals")) {
			// wrong usage of external solver, tell the user
			reason = Reason.SOLVER_CRASH_WRONG_USAGE;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.startsWith("Timeout exceeded")) {
			// timeout
			reason = Reason.SOLVER_RESPONSE_TIMEOUT;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.startsWith("ERROR: bvadd takes exactly 2 arguments")) {
			// we use bvadd with larger number of params, e.g., MatSAT complains
			reason = Reason.ULTIMATE_VIOLATES_SMT_LIB_STANDARD_AND_SOLVER_COMPLAINS;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else {
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
		}
		return new TraceCheckReasonUnknown(reason, e, exceptionCategory);
	}

}
