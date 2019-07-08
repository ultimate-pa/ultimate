/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Concatenation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegexVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Union;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Returns the loop point of a starred regex over the alphabet {@code IIcfgTransition<IcfgLocation>}.
 * The loop point is the location at which the loop starts and ends.
 * The regex has to be simple and unambiguous as defined in Tarjan's 1981 paper
 * <a href="https://dl.acm.org/citation.cfm?id=322273">Fast Algorithms for Solving Path Problems</a>.
 * This means in particular that the regex e* has L(e) ∌ ε.
 * <p>
 * This visitor must be applied to a star.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class LoopPointVisitor implements IRegexVisitor<IIcfgTransition<IcfgLocation>, IcfgLocation, Void> {

	@Override
	public IcfgLocation visit(final Star<IIcfgTransition<IcfgLocation>> star, final Void argument) {
		return star.getInner().accept(this);
	}

	@Override
	public IcfgLocation visit(final Union<IIcfgTransition<IcfgLocation>> union, final Void argument) {
		final IcfgLocation loopPoint = union.getFirst().accept(this);
		assert Objects.equals(loopPoint, union.getSecond().accept(this)) : "Loop points differ";
		return loopPoint;
	}

	@Override
	public IcfgLocation visit(final Concatenation<IIcfgTransition<IcfgLocation>> concatenation, final Void argument) {
		// optional (hard to implement and slow):
		// assert that c.getFirst() starts at location at which c.getSecond() ends
		final IcfgLocation loopPoint = concatenation.getFirst().accept(this);
		if (loopPoint != null) {
			return loopPoint;
		}
		// concatenation is of the form ε·…
		return concatenation.getSecond().accept(this);
	}

	@Override
	public IcfgLocation visit(final Literal<IIcfgTransition<IcfgLocation>> literal, final Void argument) {
		return literal.getLetter().getSource();
	}

	@Override
	public IcfgLocation visit(final Epsilon<IIcfgTransition<IcfgLocation>> epsilon, final Void argument) {
		return null;
	}

	@Override
	public IcfgLocation visit(final EmptySet<IIcfgTransition<IcfgLocation>> emptySet, final Void argument) {
		throw new IllegalArgumentException("Loop contained ∅");
	}

}
