/*
 * Code taken from https://github.com/johspaeth/PathExpression
 * Copyright (C) 2018 Johannes Spaeth
 * Copyright (C) 2018 Fraunhofer IEM, Paderborn, Germany
 * 
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-PathExpressions plug-in.
 *
 * The ULTIMATE Library-PathExpressions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-PathExpressions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-PathExpressions plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-PathExpressions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-PathExpressions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pathexpressions;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.ILabeledEdge;

public class GenericLabeledEdge<N, L> implements ILabeledEdge<N, L> {

	private final N mSource;
	private final L mLabel;
	private final N mTarget;

	public GenericLabeledEdge(N source, L label, N target) {
		this.mSource = source;
		this.mLabel = label;
		this.mTarget = target;
	}

	@Override
	public N getSource() {
		return mSource;
	}

	@Override
	public L getLabel() {
		return mLabel;
	}

	@Override
	public N getTarget() {
		return mTarget;
	}

	@Override
	public int hashCode() {
		return Objects.hash(mSource, mLabel, mTarget);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (getClass() != obj.getClass()) {
			return false;
		}
		final GenericLabeledEdge<?, ?> other = (GenericLabeledEdge<?, ?>) obj;
		return Objects.equals(mSource, other.mSource)
				&& Objects.equals(mLabel, other.mLabel)
				&& Objects.equals(mTarget, other.mTarget);
	}

	@Override
	public String toString() {
		return mSource + "–(" + mLabel + ")→" + mTarget;
	}
}
