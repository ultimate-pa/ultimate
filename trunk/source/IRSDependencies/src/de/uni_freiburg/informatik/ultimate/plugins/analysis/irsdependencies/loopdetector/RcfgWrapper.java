/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 * Simple wrapper for RCFGs to the {@link IGraph} interface used by
 * {@link AStar}.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class RcfgWrapper implements IGraph<IcfgLocation, IcfgEdge> {

	@Override
	public IcfgLocation getTarget(final IcfgEdge edge) {
		return edge.getTarget();
	}

	@Override
	public IcfgLocation getSource(final IcfgEdge edge) {
		return edge.getSource();
	}

	@Override
	public Collection<IcfgEdge> getOutgoingEdges(final IcfgLocation vertice) {
		return vertice.getOutgoingEdges();
	}

	@Override
	public boolean beginScope(final IcfgEdge edge) {
		return edge instanceof Call;
	}

	@Override
	public boolean endScope(final IcfgEdge edge) {
		return edge instanceof Return;
	}
}
