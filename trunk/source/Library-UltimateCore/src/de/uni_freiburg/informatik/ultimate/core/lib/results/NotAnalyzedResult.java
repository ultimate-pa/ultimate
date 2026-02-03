/*
 * Copyright (C) 2026 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;

/**
 * Result to store that we did not check if a specification given at some location holds.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 *            Type of the location
 */
public class NotAnalyzedResult<ELEM extends IElement> extends AbstractResultAtElement<ELEM> {
	private final Check mCheckedSpecification;

	public NotAnalyzedResult(final String plugin, final ELEM position) {
		super(position, plugin);
		final Check check = Check.getAnnotation(position);
		if (check == null) {
			mCheckedSpecification = new Check(Spec.UNKNOWN);
		} else {
			mCheckedSpecification = check;
		}
	}

	@Override
	public String getShortDescription() {
		return "Not analyzed if " + mCheckedSpecification.getPositiveMessage();
	}

	@Override
	public String getLongDescription() {
		return getShortDescription();
	}
}
