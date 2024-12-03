/*
 * Copyright (C) 2024 Pascal Walter (walterp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieIdExtractor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;

public class InvariantResultTransformer {

	private InvariantResultTransformer() {
		// Utility
		// This class could serve for more purposes in the future and also allow
		// instances if needed but right now it's really just to have the extraction
		// outside of other classes it doesn't belong to. In the future perhaps it could
		// post-process for several reqcheck properties such as e.g., vacuity too.
	}

	public static Set<String> extractRedundancySet(final Expression invariant) {
		final BoogieIdExtractor bid = new BoogieIdExtractor();
		bid.processExpression(invariant);
		return bid.getIds().stream().filter(id -> (id.endsWith("_total_pc") || id.endsWith("_total")))
				.map(id -> id.split("_ct")[0]).collect(Collectors.toSet());
	}
}
