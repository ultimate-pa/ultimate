/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util;

import java.math.BigDecimal;

/**
 * Methods for dealing with {@link BigDecimal}s.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class BigDecimalSanitizer {
	/**
	 * Accounts for found problems when passing values by string directly to BigDecimal, in order to avoid
	 * NumberFormatExceptions.
	 *
	 * @param val
	 *            The value as string.
	 * @return A new {@link BigDecimal} object that contains the given value. It is also possible that an exception is
	 *         thrown when the object is created if the given value is invalid or not handled.
	 */
	public static BigDecimal sanitizeBigDecimalValue(final String val) {
		if (val.contains("/")) {
			final String[] twoParts = val.split("/");
			if (twoParts.length != 2) {
				throw new NumberFormatException("Not a valid division value: " + val);
			}
			final BigDecimal one = new BigDecimal(twoParts[0]);
			final BigDecimal two = new BigDecimal(twoParts[1]);
			return one.divide(two);
		}
		return new BigDecimal(val);
	}
}
