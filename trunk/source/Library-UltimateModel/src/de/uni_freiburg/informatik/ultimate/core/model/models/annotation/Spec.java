/*
 * Copyright (C) 2023 Manuel Bentele
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

package de.uni_freiburg.informatik.ultimate.core.model.models.annotation;

import java.util.Set;

/**
 * Defines specification types for arbitrary checks and analyzes.
 * 
 * @author Manuel Bentele
 */
public enum Spec {

	// @formatter:off
	/*-------------------------------------------------------------------------------------------------------------
	 * Generic specification types.
	 *-----------------------------------------------------------------------------------------------------------*/
	/**
	 * Not further specified or unknown.
	 */
	UNKNOWN(Group.GENERIC,
			"unknown kind of specification holds",
			"unknown kind of specification may be violated"),
	/**
	 * An LTL property.
	 */
	LTL(Group.GENERIC,
			"LTL property holds",
			"LTL property may be violated"),

	/*-------------------------------------------------------------------------------------------------------------
	 * Program specification types.
	 *-----------------------------------------------------------------------------------------------------------*/
	/**
	 * Array Index out of bounds error.
	 */
	ARRAY_INDEX(Group.PROGRAM,
			"array index is always in bounds",
			"array index can be out of bounds"),
	/**
	 * Pre condition violated.
	 */
	PRE_CONDITION(Group.PROGRAM,
			"procedure precondition always holds",
			"procedure precondition can be violated"),
	/**
	 * Post condition violated.
	 */
	POST_CONDITION(Group.PROGRAM,
			"procedure postcondition always holds",
			"procedure postcondition can be violated"),
	/**
	 * Invariant violated.
	 */
	INVARIANT(Group.PROGRAM,
			"loop invariant is valid",
			"loop invariant can be violated"),
	/**
	 * Assert statement violated.
	 */
	ASSERT(Group.PROGRAM,
			"assertion always holds",
			"assertion can be violated"),
	/**
	 * Devision by zero error.
	 */
	DIVISION_BY_ZERO(Group.PROGRAM,
			"division by zero can never occur",
			"possible division by zero"),
	/**
	 * Integer overflow error.
	 */
	INTEGER_OVERFLOW(Group.PROGRAM,
			"integer overflow can never occur",
			"integer overflow possible"),
	/**
	 * Tried to access unallocated memory.
	 */
	MEMORY_DEREFERENCE(Group.PROGRAM,
			"pointer dereference always succeeds",
			"pointer dereference may fail"),
	/**
	 * Memory leak detected. I.e. missing free!
	 */
	MEMORY_LEAK(Group.PROGRAM,
			"all allocated memory was freed",
			"not all allocated memory was freed"),
	/**
	 * Free of unallocated pointer.
	 */
	MEMORY_FREE(Group.PROGRAM,
			"free always succeeds",
			"free of unallocated memory possible"),
	/**
	 * Free of unallocated pointer.
	 */
	MALLOC_NONNEGATIVE(Group.PROGRAM,
			"input of malloc is always non-negative",
			"input of malloc can be negative"),
	/**
	 * Pointer arithmetic that is not allowed by C. E.g. - computing the difference of two pointers that point to
	 * completely different arrays - comparing pointers that point to completely different arrays
	 */
	ILLEGAL_POINTER_ARITHMETIC(Group.PROGRAM,
			"pointer arithmetic is always legal",
			"comparison of incompatible pointers"),
	/**
	 * Error function reachable.
	 */
	ERROR_FUNCTION(Group.PROGRAM,
			"call to the error function is unreachable",
			"a call to the error function is reachable"),
	/**
	 * Invariant of a correctness witness
	 */
	WITNESS_INVARIANT(Group.PROGRAM,
			"invariant of correctness witness holds",
			"invariant of correctness witness can be violated"),
	/**
	 * Unsigned int overflow
	 */
	UINT_OVERFLOW(Group.PROGRAM,
			"there are no unsigned integer over- or underflows",
			"an unsigned integer over- or underflow may occur"),
	/**
	 * Undefined behavior according to the standard
	 */
	UNDEFINED_BEHAVIOR(Group.PROGRAM,
			"there is no undefined behavior",
			"undefined behavior may occur"),
	/**
	 * Check if a petrified ICFG does provide enough thread instances.
	 */
	SUFFICIENT_THREAD_INSTANCES(Group.PROGRAM,
			"petrification did provide enough thread instances (tool internal message)",
			"petrification did not provide enough thread instances (tool internal message)"),
	/**
	 * Check data races in concurrent programs.
	 */
	DATA_RACE(Group.PROGRAM,
			"there are no data races",
			"the program contains a data race"),
	/***
	 * Satisfiability of constraint Horn clauses
	 */
	CHC_SATISFIABILITY(Group.PROGRAM,
			"the set of constraint Horn clauses is satisfiable",
			"the set of constraint Horn clauses is unsatisfiable"),

	/*-------------------------------------------------------------------------------------------------------------
	 * Requirement specification types.
	 *-----------------------------------------------------------------------------------------------------------*/
	/**
	 * Checks for rt-inconsistency.
	 */
	RTINCONSISTENT(Group.REQUIREMENT,
			"rt-consistent",
			"rt-inconsistent"),
	/**
	 * Checks for vacuity.
	 */
	VACUOUS(Group.REQUIREMENT,
			"non-vacuous",
			"vacuous"),
	/**
	 * Checks for consistency.
	 */
	CONSISTENCY(Group.REQUIREMENT,
			"consistent",
			"inconsistent"),
	/**
	 * Checks for incompleteness.
	 */
	INCOMPLETE(Group.REQUIREMENT,
			"complete",
			"incomplete");
	// @formatter:on

	/**
	 * Specification groups to classify specification types.
	 */
	public enum Group {
		// @formatter:off
		GENERIC,
		PROGRAM,
		REQUIREMENT;
		// @formatter:on
	}

	/**
	 * Positive fallback message if specification type does not define any default positive message.
	 */
	private static final String FALLBACK_POSITIVE_MESSAGE = "a specification is correct but has no positive message";
	/**
	 * Negative fallback message if specification type does not define any default negative message.
	 */
	private static final String FALLBACK_NEGATIVE_MESSAGE =
			"a specification may be violated but has no negative message";

	/**
	 * Group of a specification type.
	 */
	private final Spec.Group mGroup;
	/**
	 * Default positive message of a specification type.
	 */
	private final String mDefaultPosMsg;
	/**
	 * Default negative message of a specification type.
	 */
	private final String mDefaultNegMsg;

	/**
	 * Create a new specification type.
	 * 
	 * @param group
	 *            specification group for the specification type.
	 */
	Spec(final Spec.Group group) {
		this(group, null, null);
	}

	/**
	 * Create a new specification type.
	 * 
	 * @param group
	 *            specification group for the specification type.
	 * @param defaultPosMsg
	 *            default positive message for the specification type.
	 * @param defaultNegMsg
	 *            default negative message for the specification type.
	 */
	Spec(final Spec.Group group, final String defaultPosMsg, final String defaultNegMsg) {
		mGroup = group;
		mDefaultPosMsg = defaultPosMsg;
		mDefaultNegMsg = defaultNegMsg;
	}

	/**
	 * Check if specification type is part of the given group.
	 * 
	 * @param group
	 *            specification group for the check.
	 * 
	 * @return {@code true} if specification type is part of the given group, otherwise {@link false}.
	 */
	public boolean isInGroup(final Spec.Group group) {
		return mGroup == group;
	}

	/**
	 * Check if specification type is part of a set of given groups.
	 * 
	 * @param groups
	 *            set of specification group for the check.
	 * 
	 * @return {@code true} if specification type is part a set of given groups, otherwise {@link false}.
	 */
	public boolean isInGroups(final Set<Spec.Group> groups) {
		return groups.contains(mGroup);
	}

	/**
	 * Return the default message of a specification type depending on the default message.
	 * 
	 * If the given default message is a valid message of the specification type, then return the given default message.
	 * Otherwise return the specified fallback message.
	 * 
	 * @param defaultMsg
	 *            default message of the specification type.
	 * @param fallbackMsg
	 *            fallback message for the specification type.
	 * 
	 * @return default message for the specification type.
	 */
	private String getDefaultMessage(final String defaultMsg, final String fallbackMsg) {
		return (defaultMsg == null) ? String.format("%s: %s", fallbackMsg, this) : defaultMsg;
	}

	/**
	 * Return the default positive message of the specification type.
	 * 
	 * If there is no positive default message for the specification type defined, the
	 * {@link #FALLBACK_POSITIVE_MESSAGE} is returned.
	 * 
	 * @return default positive message of the specification type.
	 */
	public String getDefaultPositiveMessage() {
		return getDefaultMessage(mDefaultPosMsg, FALLBACK_POSITIVE_MESSAGE);
	}

	/**
	 * Return the default negative message of the specification type.
	 * 
	 * If there is no negative default message for the specification type defined, the
	 * {@link #FALLBACK_NEGATIVE_MESSAGE} is returned.
	 * 
	 * @return default negative message of the specification type.
	 */
	public String getDefaultNegativeMessage() {
		return getDefaultMessage(mDefaultNegMsg, FALLBACK_NEGATIVE_MESSAGE);
	}
}