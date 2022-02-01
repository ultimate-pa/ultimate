/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public interface IAbstractDomain<STATE extends IAbstractState<STATE>, ACTION> {

	/**
	 * This method is called before the fixpoint computation begins. You can use it to prepare for reporting of
	 * domain-specific statistics.
	 *
	 * @param objects
	 *            You can pass multiple objects that should be used by the abstract domain. The domain should do the
	 *            check for the types and casts of the objects. Calling this method with objects that cannot be handled
	 *            by the domain should not lead to errors.
	 */
	default void beforeFixpointComputation(final Object... objects) {
		// default is doing nothing
	}

	/**
	 * @return A new state of the current abstract domain representing &top;.
	 */
	STATE createTopState();

	/**
	 * @return A new state of the current abstract domain representing &bot;.
	 */
	STATE createBottomState();

	/**
	 * @return The widening operator appropriate for the current abstract domain.
	 */
	IAbstractStateBinaryOperator<STATE> getWideningOperator();

	/**
	 * @return The post operator for the current abstract domain.
	 */
	default IAbstractPostOperator<STATE, ACTION> getPostOperator() {
		throw new UnsupportedOperationException("This domain does not support the post operator");
	}

	/**
	 * @return The pre operator for the current abstract domain.
	 */
	default IAbstractTransformer<STATE, ACTION> getPreOperator() {
		throw new UnsupportedOperationException("This domain does not support the pre operator");
	}

	/**
	 * Determines whether a given term is abstractable in the abstract domain.
	 *
	 * @param term
	 *            The term to check.
	 * @return <code>true</code> iff the term is abstractable, <code>false</code> otherwise.
	 */
	default boolean isAbstractable(final Term term) {
		return false;
	}

	/**
	 * This setting defines whether {@link IAbstractPostOperator#apply(IAbstractState, IAbstractState, Object)} is
	 * called with a <tt>stateAfterLeaving</tt> or with a <tt>hierachical pre state</tt> as second argument if the
	 * transition is leaving a scope.
	 *
	 * @return true iff {@link IAbstractPostOperator#apply(IAbstractState, IAbstractState, Object)} of this domain uses
	 *         an <tt>hierachical pre state</tt> as second argument, false if it uses an <tt>stateAfterLeaving</tt>.
	 */
	default boolean useHierachicalPre() {
		return false;
	}

	/**
	 * This method is called after the fixpoint computation ends. You can use it to report domain-specific statistics
	 * after a run.
	 *
	 * @param result
	 *            the result of the fixpoint computation (which contains, e.g., the set of fixpoints)
	 */
	default <LOC> void afterFixpointComputation(final IAbstractInterpretationResult<STATE, ACTION, LOC> result) {
		// default is doing nothing
	}

	/**
	 * @return The name of the domain. If the domain is a domain comprising several subdomains, this method can be used
	 *         to further classify the domain. See, e.g., {@link CompoundDomain#domainDescription}.
	 */
	default String domainDescription() {
		return getClass().getSimpleName();
	}
}
