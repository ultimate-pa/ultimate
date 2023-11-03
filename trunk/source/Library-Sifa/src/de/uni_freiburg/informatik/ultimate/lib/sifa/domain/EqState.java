/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class wraps an {@link EqConstraint} as an abstract state for the {@link EqDomain}.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class EqState implements IAbstractState<EqState> {
	private final EqConstraint<EqNode> mConstraint;

	public EqState(final EqConstraint<EqNode> constraint) {
		mConstraint = constraint;
	}

	@Override
	public Term toTerm(final Script script) {
		return mConstraint.getTerm(script);
	}

	@Override
	public EqState join(final EqState other) {
		final EqConstraint<EqNode> constraint = mConstraint.join(other.mConstraint);
		constraint.freezeIfNecessary();
		return new EqState(constraint);
	}

	@Override
	public EqState widen(final EqState other) {
		final EqConstraint<EqNode> constraint = mConstraint.widen(other.mConstraint);
		constraint.freezeIfNecessary();
		return new EqState(constraint);
	}

	@Override
	public boolean isBottom() {
		return mConstraint.isBottom();
	}

}
