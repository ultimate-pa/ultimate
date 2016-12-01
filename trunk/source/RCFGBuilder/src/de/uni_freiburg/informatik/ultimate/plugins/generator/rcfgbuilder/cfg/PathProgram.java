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

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PathProgram extends BasePayloadContainer implements IIcfg {

	private static final long serialVersionUID = 6691317791231881900L;
	private final IIcfg mOriginalIcfg;
	private final String mIdentifier;
	// private Map<IcfgLocation,IAction> m

	public PathProgram(final String identifier, final IIcfg originalIcfg, final Set<IAction> allowedTransitions) {
		mOriginalIcfg = originalIcfg;
		mIdentifier = identifier;
	}

	@Override
	public Map<String, Map<String, BoogieIcfgLocation>> getProgramPoints() {
		return null;
	}

	@Override
	public Map<String, BoogieIcfgLocation> getProcedureEntryNodes() {
		return null;
	}

	@Override
	public Map<String, BoogieIcfgLocation> getProcedureExitNodes() {
		return null;
	}

	@Override
	public Map<String, Collection<BoogieIcfgLocation>> getProcedureErrorNodes() {
		return null;
	}

	@Override
	public CodeBlockFactory getCodeBlockFactory() {
		return mOriginalIcfg.getCodeBlockFactory();
	}

	@Override
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mOriginalIcfg.getCfgSmtToolkit();
	}

	@Override
	public String getIdentifier() {
		return mIdentifier;
	}

	private final class LazyIcfgLocation extends IcfgLocation {

		private static final long serialVersionUID = 1L;
		private final boolean mInitialized;
		private final IcfgLocation mBacking;

		protected LazyIcfgLocation(final IcfgLocation backing) {
			super(backing.getDebugIdentifier(), backing.getProcedure());
			mInitialized = false;
			mBacking = backing;
		}

		@Override
		public List<IcfgEdge> getIncomingEdges() {
			if (!mInitialized) {
				init();
			}
			return super.getIncomingEdges();
		}

		@Override
		public List<IcfgEdge> getOutgoingEdges() {
			if (!mInitialized) {
				init();
			}
			return super.getOutgoingEdges();
		}

		private void init() {

		}

	}

	private final class LazyInternalAction extends IcfgInternalAction {
		public LazyInternalAction(final IcfgLocation source, final IcfgLocation target, final IPayload payload,
				final UnmodifiableTransFormula transFormula) {
			super(source, target, payload, transFormula);
		}
	}
}
