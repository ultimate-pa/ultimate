/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE UltimateUtil Library.
 *
 * The ULTIMATE UltimateUtil Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UltimateUtil Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UltimateUtil Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UltimateUtil Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UltimateUtil Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.simplifier;

import java.util.Collection;
import java.util.Iterator;

/**
 * Describes an decorator that provides an input for {@link NormalFormTransformer}.
 *
 * @author dietsch@informatik.uni-freiburg.de
 * @param <E>
 */
public interface INormalFormable<E> {

	E changeForall(E oldForAll, E operand);

	E makeAnd(E first, E second);

	Collection<? extends E> normalizeNesting(E formula, E subformula);

	E makeFalse();

	E makeTrue();

	E changeExists(E oldExists, E operand);

	E makeOr(Iterator<E> operands);

	E makeAnd(Iterator<E> operands);

	E makeNot(E operand);

	E getOperand(E formula);

	E rewritePredNotEquals(E atom);

	E negatePred(E atom);

	Iterator<E> getOperands(E formula);

	/**
	 * @return true iff formula is of the form x or c
	 */
	boolean isAtom(E formula);

	/**
	 * @return true iff the formula is of the form x or !x
	 */
	boolean isLiteral(E formula);

	/**
	 * @return true iff formula is of the form !&phi;
	 */
	boolean isNot(E formula);

	/**
	 * @return true iff formula is of the form &phi; && &phi;
	 */
	boolean isAnd(E formula);

	/**
	 * @return true iff formula is of the form &phi; || &phi;
	 */
	boolean isOr(E formula);

	/**
	 * @return true iff formula is of the form &exist;x &phi;
	 */
	boolean isExists(E formula);

	/**
	 * @return true iff formula is of the form &forall;x &phi;
	 */
	boolean isForall(E formula);

	boolean isEqual(E one, E other);

	boolean isTrue(E formula);

	boolean isFalse(E formula);
}
