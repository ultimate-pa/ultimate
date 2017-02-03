/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;

/**
 * Result that reports that a counter example for an LTL property was found and that it is finite.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class LTLFiniteCounterExampleResult<ELEM extends IElement, TE extends IElement, E>
		extends CounterExampleResult<ELEM, TE, E> {

	public LTLFiniteCounterExampleResult(final ELEM position, final String plugin,
			final IBacktranslationService translatorSequence, final IProgramExecution<TE, E> pe, final Check check) {
		super(annotatePositionWithCheck(position, check), plugin, translatorSequence, pe);
	}

	private static <ELEM extends IElement> ELEM annotatePositionWithCheck(final ELEM position, final Check check) {
		if (check == null || !check.getSpec().equals(Spec.LTL)) {
			throw new IllegalArgumentException("You cannot use " + LTLFiniteCounterExampleResult.class.getSimpleName()
					+ " for specs different from LTL");
		}
		check.annotate(position);
		return position;
	}
}
