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
 * Positive default message provider for {@link Check} specifications that are checked.
 * 
 * @author Manuel Bentele
 */
public class CheckPositiveMessageProvider extends CheckMessageProvider {

	@Override
	public String getDefaultMessage(final Spec spec) {
		switch (spec) {
		case ARRAY_INDEX:
			return "array index is always in bounds";
		case PRE_CONDITION:
			return "procedure precondition always holds";
		case POST_CONDITION:
			return "procedure postcondition always holds";
		case INVARIANT:
			return "loop invariant is valid";
		case ASSERT:
			return "assertion always holds";
		case DIVISION_BY_ZERO:
			return "division by zero can never occur";
		case INTEGER_OVERFLOW:
			return "integer overflow can never occur";
		case MEMORY_DEREFERENCE:
			return "pointer dereference always succeeds";
		case MEMORY_LEAK:
			return "all allocated memory was freed";
		case MEMORY_FREE:
			return "free always succeeds";
		case MALLOC_NONNEGATIVE:
			return "input of malloc is always non-negative";
		case ILLEGAL_POINTER_ARITHMETIC:
			return "pointer arithmetic is always legal";
		case ERROR_FUNCTION:
			return "call to the error function is unreachable";
		case WITNESS_INVARIANT:
			return "invariant of correctness witness holds";
		case UNKNOWN:
			return "unknown kind of specification holds";
		case UINT_OVERFLOW:
			return "there are no unsigned integer over- or underflows";
		case UNDEFINED_BEHAVIOR:
			return "there is no undefined behavior";
		case RTINCONSISTENT:
			return "rt-consistent";
		case VACUOUS:
			return "non-vacuous";
		case CONSISTENCY:
			return "consistent";
		case INCOMPLETE:
			return "complete";
		case SUFFICIENT_THREAD_INSTANCES:
			return "petrification did provide enough thread instances (tool internal message, not intended for end users)";
		case DATA_RACE:
			return "there are no data races";
		case CHC_SATISFIABILITY:
			return "the set of constraint Horn clauses is satisfiable";
		default:
			return "a specification is correct but has no positive message: " + spec;
		}
	}
}
