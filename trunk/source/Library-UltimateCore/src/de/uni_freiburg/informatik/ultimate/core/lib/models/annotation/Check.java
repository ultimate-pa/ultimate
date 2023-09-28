/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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

package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.EnumSet;
import java.util.Iterator;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;

/**
 * Specification that should be checked at position
 *
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @author Matthias Heizmann
 */
public class Check extends ModernAnnotations {

	private static final String MSG_AND = " and ";

	public enum Spec {
		/**
		 * Array Index out of bounds error.
		 */
		ARRAY_INDEX,
		/**
		 * Pre condition violated.
		 */
		PRE_CONDITION,
		/**
		 * Post condition violated.
		 */
		POST_CONDITION,
		/**
		 * Invariant violated.
		 */
		INVARIANT,
		/**
		 * Assert statement violated.
		 */
		ASSERT,
		/**
		 * Devision by zero error.
		 */
		DIVISION_BY_ZERO,
		/**
		 * Integer overflow error.
		 */
		INTEGER_OVERFLOW,
		/**
		 * Tried to access unallocated memory.
		 */
		MEMORY_DEREFERENCE,
		/**
		 * Memory leak detected. I.e. missing free!
		 */
		MEMORY_LEAK,
		/**
		 * Free of unallocated pointer.
		 */
		MEMORY_FREE,
		/**
		 * Free of unallocated pointer.
		 */
		MALLOC_NONNEGATIVE,
		/**
		 * Pointer arithmetic that is not allowed by C. E.g. - computing the difference of two pointers that point to
		 * completely different arrays - comparing pointers that point to completely different arrays
		 */
		ILLEGAL_POINTER_ARITHMETIC,
		/**
		 * Error function reachable.
		 */
		ERROR_FUNCTION,
		/**
		 * Not further specified or unknown.
		 */
		UNKNOWN,
		/**
		 * An LTL property
		 */
		LTL,
		/**
		 * Invariant of a correctness witness
		 */
		WITNESS_INVARIANT,
		/**
		 * Unsigned int overflow
		 */
		UINT_OVERFLOW,
		/**
		 * Undefined behavior according to the standard
		 */
		UNDEFINED_BEHAVIOR,
		/**
		 * Check for requirements. Checks for rt-inconsistency.
		 */
		RTINCONSISTENT,
		/**
		 * Check for requirements. Checks for vacuity.
		 */
		VACUOUS,
		/**
		 * Check for requirements. Checks for consistency.
		 */
		CONSISTENCY,
		/**
		 * Check for requirements. Checks for incompleteness.
		 */
		INCOMPLETE,
		/**
		 * Check for requirements. Checks if two PEAs accept each others complement language.
		 */
		COMPLEMENT,
		/**
		 * Check for requirements. Checks for redundancy.
		 */
		REDUNDANCY,
		/**
		 * Check if a petrified ICFG does provide enough thread instances.
		 */
		SUFFICIENT_THREAD_INSTANCES,

		DATA_RACE,

		/***
		 * Satisfiability of constraint Horn clauses
		 */
		CHC_SATISFIABILITY,

	}

	private static final long serialVersionUID = -3753413284642976683L;

	private static final String KEY = Check.class.getName();

	@Visualizable
	private final Set<Spec> mSpec;

	private final Function<Spec, String> mPosMsgProvider;

	private final Function<Spec, String> mNegMsgProvider;

	public Check(final Check.Spec spec) {
		this(EnumSet.of(spec));
	}

	public Check(final Check.Spec spec, final Function<Spec, String> funPositiveMessageProvider,
			final Function<Spec, String> funNegativeMessageProvider) {
		this(EnumSet.of(spec), funPositiveMessageProvider, funNegativeMessageProvider);
	}

	public Check(final Set<Spec> newSpec) {
		this(newSpec, Check::getDefaultPositiveMessage, Check::getDefaultNegativeMessage);
	}

	public Check(final Set<Spec> newSpec, final Function<Spec, String> funPositiveMessageProvider,
			final Function<Spec, String> funNegativeMessageProvider) {
		assert !newSpec.isEmpty();
		mSpec = newSpec;
		mPosMsgProvider = funPositiveMessageProvider;
		mNegMsgProvider = funNegativeMessageProvider;
	}

	public Set<Spec> getSpec() {
		return mSpec;
	}

	public String getPositiveMessage() {
		return getMessage(mPosMsgProvider);
	}

	public String getNegativeMessage() {
		return getMessage(mNegMsgProvider);
	}

	private String getMessage(final Function<Spec, String> funMessageProvider) {
		final Iterator<Spec> iter = mSpec.iterator();
		if (mSpec.size() == 1) {
			return funMessageProvider.apply(iter.next());
		}

		final StringBuilder sb = new StringBuilder();
		while (iter.hasNext()) {
			sb.append(funMessageProvider.apply(iter.next())).append(MSG_AND);
		}
		sb.delete(sb.length() - MSG_AND.length(), sb.length());
		return sb.toString();
	}

	public static String getDefaultPositiveMessage(final Spec spec) {
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
		case COMPLEMENT:
			return "complements of each other";
		case REDUNDANCY:
			return "redundant";
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

	public static String getDefaultNegativeMessage(final Spec spec) {
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
		case COMPLEMENT:
			return "not complements of each other";
		case REDUNDANCY:
			return "non-redundant";
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

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other == null) {
			return this;
		}
		if (other == this) {
			return this;
		}
		if (!(other instanceof Check)) {
			throw new UnmergeableAnnotationsException(this, other);
		}
		final Check otherCheck = (Check) other;

		final EnumSet<Spec> newSpec = EnumSet.copyOf(mSpec);
		newSpec.addAll(otherCheck.getSpec());
		// note: automatic merging looses all information about message providers and uses the default ones
		return new Check(newSpec);
	}

	/**
	 * Adds this Check object to the annotations of a IElement.
	 *
	 * @param node
	 *            the element
	 */
	public void annotate(final IElement node) {
		node.getPayload().getAnnotations().put(KEY, this);
	}

	/**
	 * Return the checked specification that is checked at this location or null.
	 */
	public static Check getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (Check) a);
	}

	public static Check mergeCheck(final Check one, final Check other) {
		if (one == null) {
			return other;
		}
		if (other == null) {
			return one;
		}
		return (Check) one.merge(other);
	}

	@Override
	public String toString() {
		return mSpec.stream().map(Spec::toString).collect(Collectors.joining(MSG_AND));
	}

	@Override
	public int hashCode() {
		return toString().hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Check other = (Check) obj;
		if (mSpec == null) {
			if (other.mSpec != null) {
				return false;
			}
		} else if (!mSpec.equals(other.mSpec)) {
			return false;
		}
		return true;
	}

}
