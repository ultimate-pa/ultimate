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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public interface IAbstractDomain<STATE extends IAbstractState<STATE>, ACTION> {

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

	default IAbstractTransformer<STATE, ACTION> getPreOperator() {
		throw new UnsupportedOperationException("This domain does not support the pre operator");
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
}
