/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A predicate annotated with additional data.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <P>
 *            The type of underlying predicates
 * @param <A>
 *            The type of additional data
 */
public abstract class AnnotatedPredicate<P extends IPredicate, A> implements IPredicate {
	protected final P mUnderlying;
	protected final A mAnnotation;

	protected AnnotatedPredicate(final P underlying, final A annotation) {
		mUnderlying = Objects.requireNonNull(underlying);
		mAnnotation = annotation;
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mUnderlying.getVars();
	}

	@Override
	public Set<IProgramFunction> getFuns() {
		return mUnderlying.getFuns();
	}

	@Override
	public Term getFormula() {
		return mUnderlying.getFormula();
	}

	@Override
	public Term getClosedFormula() {
		return mUnderlying.getClosedFormula();
	}

	public P getUnderlying() {
		return mUnderlying;
	}

	@Override
	public int hashCode() {
		return Objects.hash(mAnnotation, mUnderlying);
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
		final AnnotatedPredicate<?, ?> other = (AnnotatedPredicate<?, ?>) obj;
		return Objects.equals(mAnnotation, other.mAnnotation) && Objects.equals(mUnderlying, other.mUnderlying);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName() + " [underlying: " + mUnderlying + ", annotation: " + mAnnotation + "]";
	}
}
