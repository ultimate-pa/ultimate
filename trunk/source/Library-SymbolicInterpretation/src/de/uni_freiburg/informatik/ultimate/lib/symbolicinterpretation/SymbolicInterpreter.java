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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Annotates given program locations with predicates over-approximating the actually reachable concrete states at that
 * locations.
 *
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class SymbolicInterpreter {

	private final IIcfg<IcfgLocation> mIcfg;
	private final Collection<IcfgLocation> mLocationsOfInterest;

	public SymbolicInterpreter(final IIcfg<IcfgLocation> icfg, final Collection<IcfgLocation> locationsOfInterest) {
		mIcfg = icfg;
		mLocationsOfInterest = locationsOfInterest;

		// locationsOfInterest.stream().findFirst().get().getProcedure()
		icfg.getInitialNodes();
		final HashRelation<String, String> cg = new HashRelation<>();
		new IcfgEdgeIterator(icfg).asStream().filter(a -> a instanceof IIcfgCallTransition<?>)
				.forEach(a -> cg.addPair(a.getSource().getProcedure(), a.getTarget().getProcedure()));
	}
}
