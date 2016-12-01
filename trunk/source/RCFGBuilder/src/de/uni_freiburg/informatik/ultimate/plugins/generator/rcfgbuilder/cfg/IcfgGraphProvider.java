/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class IcfgGraphProvider {

	public static VisualizationNode getVisualizationGraph(final IIcfg cont) {
		final IExplicitEdgesMultigraph<IcfgLocation, IcfgEdge, IcfgLocation, IcfgEdge, VisualizationNode> artificialRoot =
				getVirtualRoot(cont);
		return new VisualizationNode(artificialRoot);
	}

	public static IExplicitEdgesMultigraph<IcfgLocation, IcfgEdge, IcfgLocation, IcfgEdge, VisualizationNode>
			getVirtualRoot(final IIcfg cont) {
		final IcfgVirtualRoot artificialRoot = new IcfgVirtualRoot();
		if (cont instanceof IAnnotations) {
			artificialRoot.getPayload().getAnnotations().put(cont.getClass().getSimpleName(), (IAnnotations) cont);
		}
		for (final Entry<String, BoogieIcfgLocation> entry : cont.getProcedureEntryNodes().entrySet()) {
			final IcfgVirtualRootEdge edge = new IcfgVirtualRootEdge(artificialRoot, entry.getValue());
			edge.redirectSource(artificialRoot);
			edge.redirectTarget(entry.getValue());
		}
		return artificialRoot;
	}

	private static final class IcfgVirtualRoot extends IcfgLocation {

		private static final long serialVersionUID = 7322581913329216222L;

		protected IcfgVirtualRoot() {
			super("ARTIFICIAL-ROOT", "");
		}
	}

	private static final class IcfgVirtualRootEdge extends IcfgEdge {

		private static final long serialVersionUID = 7322581913329216222L;

		protected IcfgVirtualRootEdge(final IcfgLocation source, final IcfgLocation target) {
			super(source, target, null);
		}
	}
}
