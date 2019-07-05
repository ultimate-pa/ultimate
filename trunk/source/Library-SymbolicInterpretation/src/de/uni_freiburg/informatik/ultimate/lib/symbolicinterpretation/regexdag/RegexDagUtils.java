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
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.LoopPointVisitor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class RegexDagUtils {

	public static IcfgLocation singleSinkLocation(final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay) {
		final Set<IcfgLocation> sinkLocations = sinkLocations(dag, overlay);
		if (sinkLocations.size() != 1) {
			throw new IllegalArgumentException("Expected one sink location but found " + sinkLocations.size());
		}
		return sinkLocations.iterator().next();
	}

	/**
	 * Returns IcfgLocations having a path to the dag's sink on which no other IcfgLocation occurs.
	 */
	public static Set<IcfgLocation> sinkLocations(final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay) {

		// TODO fix overlay usage. Overlay may have multiple sinks. Sink from overlay my be different than sink from dag

		final Set<IcfgLocation> sinkLocs = new HashSet<>();
		final Queue<RegexDagNode<IIcfgTransition<IcfgLocation>>> worklist = new ArrayDeque<>();
		worklist.addAll(overlay.sinks(dag));
		while (!worklist.isEmpty()) {
			final RegexDagNode<IIcfgTransition<IcfgLocation>> node = worklist.remove();
			final IRegex<IIcfgTransition<IcfgLocation>> regex = node.getContent();
			if (regex instanceof Literal<?>) {
				sinkLocs.add(((Literal<IIcfgTransition<IcfgLocation>>) regex).getLetter().getTarget());
			} else if (regex instanceof Star<?>) {
				sinkLocs.add(regex.accept(new LoopPointVisitor()));
			} else {
				worklist.addAll(node.getIncomingNodes());
			}
		}
		return sinkLocs;
	}

}
