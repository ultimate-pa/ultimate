/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LTL2Aut plug-in.
 * 
 * The ULTIMATE LTL2Aut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LTL2Aut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LTL2Aut plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LTL2Aut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LTL2Aut plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IVisualizable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class NWAContainer extends BasePayloadContainer implements IVisualizable {

	private static final long serialVersionUID = 1L;
	private final INestedWordAutomaton<CodeBlock, String> mNWA;

	public NWAContainer(final INestedWordAutomaton<CodeBlock, String> nwa) {
		mNWA = nwa;
	}

	public INestedWordAutomaton<CodeBlock, String> getNWA() {
		return mNWA;
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		final Collection<String> initials = mNWA.getInitialStates();

		final ArrayList<NWAVisualizationNode<String, CodeBlock>> visInitials = new ArrayList<>();
		for (final String initial : initials) {
			visInitials.add(new NWAVisualizationNode<String, CodeBlock>(mNWA, initial));
		}

		if (visInitials.size() > 1) {
			throw new UnsupportedOperationException();
		} else {
			return new VisualizationNode(visInitials.get(0));
		}
	}
}
