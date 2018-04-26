/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

/**
 * Result to store that the specification given at some location always holds. The specification at this location may
 * explicitly (e.g., there is a assert statement at this location) or implicitly (e.g. at this location a pointer is
 * dereferenced and the programming language does not allow dereference of nullpointers).
 *
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 27.03.2012
 */
public class PositiveResult<ELEM extends IElement> extends AbstractResultAtElement<ELEM> implements IResultWithCheck {
	private final Check mCheckedSpecification;

	/**
	 * Constructor.
	 *
	 * @param location
	 *            the location
	 */
	public PositiveResult(final String plugin, final ELEM position, final IBacktranslationService translatorSequence) {
		super(position, plugin, translatorSequence);
		mCheckedSpecification = ResultUtil.getCheckedSpecification(position);
	}

	@Override
	public String getShortDescription() {
		if (mCheckedSpecification == null) {
			return "some specification holds - ERROR (information lost during translation process)";
		}
		return mCheckedSpecification.getPositiveMessage();
	}

	@Override
	public String getLongDescription() {
		if (mCheckedSpecification == null) {
			return "some specification holds - ERROR (information lost during translation process)";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("For all program executions holds that ");
		sb.append(mCheckedSpecification.getPositiveMessage());
		sb.append(" at this location");
		return sb.toString();
	}

	@Override
	public Check getCheckedSpecification() {
		return mCheckedSpecification;
	}
}
