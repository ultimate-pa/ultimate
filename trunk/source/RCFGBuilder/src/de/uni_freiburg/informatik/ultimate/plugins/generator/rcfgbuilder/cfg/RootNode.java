/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ArtificialRootDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

/**
 * Root node in a Ultimate Model of a program. Information about about the program represented by this Ultimate Model
 * which can not be expressed by the recursive control flow graph are stored in a RootAnnot object stored in the Payload
 * of this RootNode. The ILocation of the RootNode should be the ILocation of the unit of a Boogie Program.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
@Deprecated
public class RootNode extends IcfgLocation {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	public RootNode(final ILocation location, final BoogieIcfgContainer rootAnnot) {
		super(ArtificialRootDebugIdentifier.DEFAULT, "rootNode");
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, rootAnnot);
		location.annotate(this);
	}

	@Deprecated
	public BoogieIcfgContainer getRootAnnot() {
		return (BoogieIcfgContainer) getPayload().getAnnotations().get(Activator.PLUGIN_ID);
	}

	@Override
	public boolean addIncoming(final IcfgEdge incoming) {
		throw new UnsupportedOperationException("RootNode has no incoming edges");
	}
}
