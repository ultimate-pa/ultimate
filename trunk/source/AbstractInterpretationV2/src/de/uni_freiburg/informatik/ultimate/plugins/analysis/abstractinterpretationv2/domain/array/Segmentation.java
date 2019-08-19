/*
 * Copyright (C) 2017 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class Segmentation {
	private final List<IProgramVar> mBounds;
	private final List<IProgramVar> mValues;

	public Segmentation(final List<IProgramVar> bounds, final List<IProgramVar> values) {
		if (bounds.size() != values.size() + 1) {
			throw new IllegalArgumentException(
					String.format("Incompatible sizes of bounds (%d) and values (%d)", bounds.size(), values.size()));
		}
		mBounds = bounds;
		mValues = values;
	}

	public List<IProgramVar> getBounds() {
		return Collections.unmodifiableList(mBounds);
	}

	public List<IProgramVar> getValues() {
		return Collections.unmodifiableList(mValues);
	}

	public IProgramVar getBound(final int i) {
		return mBounds.get(i);
	}

	public IProgramVar getValue(final int i) {
		return mValues.get(i);
	}

	public int size() {
		return mValues.size();
	}

	@Override
	public String toString() {
		final StringBuilder stringBuilder = new StringBuilder();
		for (int i = 0; i < size(); i++) {
			stringBuilder.append('[').append(getBound(i)).append("] ");
			stringBuilder.append(getValue(i)).append(' ');
		}
		stringBuilder.append('[').append(getBound(size())).append(']');
		return stringBuilder.toString();
	}

	@Override
	public int hashCode() {
		return mBounds.hashCode() + mValues.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || !(obj instanceof Segmentation)) {
			return false;
		}
		final Segmentation other = (Segmentation) obj;
		return mBounds.equals(other.mBounds) && mValues.equals(other.mValues);
	}
}
