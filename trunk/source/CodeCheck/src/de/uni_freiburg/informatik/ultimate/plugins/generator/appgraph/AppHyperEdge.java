/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;

public class AppHyperEdge extends AppEdge {

	private static final long serialVersionUID = 1L;

	private AnnotatedProgramPoint mHierLoc;
	private final IIcfgReturnTransition<?, ?> mReturnTransition;

	public AppHyperEdge(final AnnotatedProgramPoint source, final AnnotatedProgramPoint hier,
			final IIcfgReturnTransition<?, ?> returnStm, final AnnotatedProgramPoint target) {
		super(source, returnStm, target);
		mHierLoc = hier;
		mReturnTransition = returnStm;
	}

	public AnnotatedProgramPoint getHier() {
		return mHierLoc;
	}

	@Override
	public void disconnect() {
		mHierLoc.getOutgoingHyperEdges().remove(this);
		mHierLoc = null;
		super.disconnect();
	}
}
