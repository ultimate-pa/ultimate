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
import java.util.Collection;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctMatrix.WideningStepSupplier;

/**
 * Widening operator for octagons that increases bounds using a fixed set of constants. Usually, the constants are
 * collected literals of the analyzed program.
 *
 * @see OctMatrix#widenStepwise(OctMatrix, WideningStepSupplier)
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctLiteralWideningOperator implements IAbstractStateBinaryOperator<OctDomainState>, WideningStepSupplier {
	
	/**
	 * Widening steps.
	 * <p>
	 * <b>Note:</b> {@link TreeSet TreeSets} normally requires that {@code equals} is consistent with
	 * {@code compareTo(...) == 0} -- this is not the case for {@link BigDecimal} and {@link OctValue}. But the actual
	 * implementation of {@link TreeSet} (openjdk 8u40-b25) actually works in this scenario. {@code equals} is only used
	 * in methods like {@link TreeSet#contains(Object)}} or {@link TreeSet#remove(Object)}}.
	 */
	private final TreeSet<OctValue> wideningSteps;

	/**
	 * Creates a new literal widening operator. The widening operator will increase values to one of the given literals
	 * or infinity.
	 * <p>
	 * The created widening operator will use an extended set of literals. For a literal {@code l} the literals
	 * {@code -2*l}, {@code -l}, and {@code 2*l} are introduced.
	 *
	 * @param numberLiterals
	 *            Set of constants (preferable literals from the program to be analyzed)
	 */
	public OctLiteralWideningOperator(final Collection<BigDecimal> numberLiterals) {
		wideningSteps = new TreeSet<>(); // removes duplicates using method "compareTo"
		for (final BigDecimal literal : numberLiterals) {
			
			final BigDecimal literal2 = literal.add(literal); // literal * 2, since octagons store interval bounds * 2
			
			wideningSteps.add(new OctValue(literal));
			wideningSteps.add(new OctValue(literal2));
			
			// negative literals are usually represented as UnaryExpression[ARITHNEG,<literal>]
			// => negation signs get lost during literal collection
			wideningSteps.add(new OctValue(literal.negate()));
			wideningSteps.add(new OctValue(literal2.negate()));
		}
	}
	
	@Override
	public OctValue nextWideningStep(final OctValue val) {
		final OctValue ceil = wideningSteps.ceiling(val);
		return (ceil == null) ? OctValue.INFINITY : ceil;
	}

	@Override
	public OctDomainState apply(final OctDomainState first, final OctDomainState second) {
		return first.widen(second, (m, n) -> m.widenStepwise(n, this));
	}
	
}
