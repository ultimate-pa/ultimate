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

package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;

/**
 * Negative default message provider for {@link Check} specifications that are checked.
 * 
 * @author Manuel Bentele
 */
public class CheckNegativeMessageProvider extends CheckMessageProvider {

	@Override
	public String getDefaultMessage(final Spec spec) {
		switch (spec) {
		case ARRAY_INDEX:
			return "array index can be out of bounds";
		case PRE_CONDITION:
			return "procedure precondition can be violated";
		case POST_CONDITION:
			return "procedure postcondition can be violated";
		case INVARIANT:
			return "loop invariant can be violated";
		case ASSERT:
			return "assertion can be violated";
		case DIVISION_BY_ZERO:
			return "possible division by zero";
		case INTEGER_OVERFLOW:
			return "integer overflow possible";
		case MEMORY_DEREFERENCE:
			return "pointer dereference may fail";
		case MEMORY_LEAK:
			return "not all allocated memory was freed";
		case MEMORY_FREE:
			return "free of unallocated memory possible";
		case MALLOC_NONNEGATIVE:
			return "input of malloc can be negative";
		case ILLEGAL_POINTER_ARITHMETIC:
			return "comparison of incompatible pointers";
		case ERROR_FUNCTION:
			return "a call to the error function is reachable";
		case WITNESS_INVARIANT:
			return "invariant of correctness witness can be violated";
		case UNKNOWN:
			return "unknown kind of specification may be violated";
		case UINT_OVERFLOW:
			return "an unsigned integer over- or underflow may occur";
		case UNDEFINED_BEHAVIOR:
			return "undefined behavior may occur";
		case RTINCONSISTENT:
			return "rt-inconsistent";
		case VACUOUS:
			return "vacuous";
		case CONSISTENCY:
			return "inconsistent";
		case INCOMPLETE:
			return "incomplete";
		case SUFFICIENT_THREAD_INSTANCES:
			return "petrification did not provide enough thread instances (tool internal message, not intended for end users)";
		case DATA_RACE:
			return "the program contains a data race";
		case CHC_SATISFIABILITY:
			return "the set of constraint Horn clauses is unsatisfiable";
		default:
			return "a specification may be violated but has no negative message: " + spec;
		}
	}
}
