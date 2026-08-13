/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration.Linearity;

public class CivlUtils {
	private CivlUtils() {
		// static utility class should not be instantiated
	}

	static Attribute createLinearityAttribute(final Linearity linearity) {
		final String name = switch (linearity) {
		case IN -> "linear_in";
		case OUT -> "linear_out";
		case INOUT -> "linear";
		case NONE -> throw new IllegalArgumentException();
		};
		return new NamedAttribute(null, name, new Expression[0]);
	}

	static NamedAttribute createLayerAttribute(final int introductionLayer, final int disappearingLayer) {
		final var introductionLit = new IntegerLiteral(null, BoogieType.TYPE_INT, String.valueOf(introductionLayer));
		final var disappearingLit = new IntegerLiteral(null, BoogieType.TYPE_INT, String.valueOf(disappearingLayer));
		return new NamedAttribute(null, "layer", new Expression[] { introductionLit, disappearingLit });
	}

	static NamedAttribute createLayerAttribute(final int layer) {
		final var lit = new IntegerLiteral(null, BoogieType.TYPE_INT, String.valueOf(layer));
		return new NamedAttribute(null, "layer", new Expression[] { lit });
	}
}
