/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class WitnessAssumption extends ModernAnnotations {
	private static final long serialVersionUID = -3753413284642976683L;

	private static final String KEY = WitnessAssumption.class.getName();

	@Visualizable
	private final boolean mIsNegated;

	public WitnessAssumption(final boolean isNegated) {
		mIsNegated = isNegated;
	}

	public void annotate(final IElement node) {
		node.getPayload().getAnnotations().put(KEY, this);
	}

	public static WitnessAssumption getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (WitnessAssumption) a);
	}

	@Override
	public String toString() {
		return mIsNegated ? KEY + "(negated)" : KEY;
	}

	public boolean isIsNegated() {
		return mIsNegated;
	}

	@Override
	public int hashCode() {
		return Objects.hash(mIsNegated);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final WitnessAssumption other = (WitnessAssumption) obj;
		return mIsNegated == other.mIsNegated;
	}
}
