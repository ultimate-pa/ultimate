/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.decider.overallresult;

/**
 * The possible overall results of a software model checker that analyzes safety (e.g., TraceAbstraction toolchain,
 * Kojak toolchain) are these enum's elements.
 *
 * We may extends this enum in the future.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public enum SafetyCheckerOverallResult {
	SAFE,

	UNSAFE,

	UNSAFE_MEMTRACK,

	UNSAFE_DEREF,

	UNSAFE_FREE,

	UNSAFE_OVERAPPROXIMATED,

	/**
	 * Indicates that a given annotation (e.g., Floyd-Hoare annotation) is a valid
	 * proof of correctness.
	 */
	VALID_ANNOTATION,

	/**
	 * Indicates that a given annotation (e.g., Floyd-Hoare annotation) is
	 * insufficient to prove correctness.
	 */
	INVALID_ANNOTATION,

	UNKNOWN,

	SYNTAX_ERROR,

	TIMEOUT,

	UNSUPPORTED_SYNTAX,

	EXCEPTION_OR_ERROR,

	NO_RESULT
}
