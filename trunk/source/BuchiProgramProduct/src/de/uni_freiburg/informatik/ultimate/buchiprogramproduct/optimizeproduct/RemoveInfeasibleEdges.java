/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 *
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class RemoveInfeasibleEdges extends BaseProductOptimizer {

	public RemoveInfeasibleEdges(final BoogieIcfgContainer product, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		super(product, services, storage);

	}

	@Override
	protected BoogieIcfgContainer createResult(final BoogieIcfgContainer root) {
		final ArrayDeque<IcfgEdge> edges = new ArrayDeque<>();
		final HashSet<IcfgEdge> closed = new HashSet<>();

		edges.addAll(BoogieIcfgContainer.extractStartEdges(root));

		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			edges.addAll(current.getTarget().getOutgoingEdges());

			if (current instanceof CodeBlock) {
				checkCodeblock((CodeBlock) current);
			}
		}

		removeDisconnectedLocations(root);
		mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
				+ " locations because of local infeasibility");
		return root;
	}

	private void checkCodeblock(final CodeBlock cb) {
		if (cb instanceof Call || cb instanceof Return) {
			return;
		}

		final Infeasibility result = cb.getTransitionFormula().isInfeasible();

		switch (result) {
		case INFEASIBLE:
			mLogger.debug("Removing " + result + ": " + cb);
			cb.disconnectSource();
			cb.disconnectTarget();
			mRemovedEdges++;
			break;
		case NOT_DETERMINED:
			break;
		case UNPROVEABLE:
			break;
		default:
			throw new IllegalArgumentException();
		}
	}

	@Override
	public boolean isGraphChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}

}
