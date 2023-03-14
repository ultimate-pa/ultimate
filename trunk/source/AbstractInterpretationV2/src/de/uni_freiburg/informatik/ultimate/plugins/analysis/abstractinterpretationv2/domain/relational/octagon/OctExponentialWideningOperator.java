/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;

/**
 * Widening operator for octagons that increases values a binary exponential backoff.
 *
 * @see OctMatrix#widenExponential(OctMatrix, OctValue)
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctExponentialWideningOperator implements IAbstractStateBinaryOperator<OctDomainState> {
	
	private final BiFunction<OctMatrix, OctMatrix, OctMatrix> mWideningOperator;

	/**
	 * Creates a new exponential widening operator. The widening operator will set widened values above the threshold to
	 * infinity.
	 *
	 * @param threshold
	 *            Threshold value (must be smaller than infinity in order to stabilize)
	 *
	 * @see OctMatrix#widenExponential(OctMatrix, OctValue)
	 */
	public OctExponentialWideningOperator(final BigDecimal threshold) {
		final OctValue octThreshold = new OctValue(threshold);
		mWideningOperator = (m, n) -> m.widenExponential(n, octThreshold);
	}
	
	@Override
	public OctDomainState apply(final OctDomainState first, final OctDomainState second) {
		return first.widen(second, mWideningOperator);
	}
}
