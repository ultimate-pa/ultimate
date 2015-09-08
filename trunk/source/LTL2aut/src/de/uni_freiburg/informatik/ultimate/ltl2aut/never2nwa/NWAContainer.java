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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.model.structure.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.model.structure.IVisualizable;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class NWAContainer extends BasePayloadContainer implements IVisualizable {

	private static final long serialVersionUID = 1L;
	private final NestedWordAutomaton<CodeBlock, String> mNWA;

	public NWAContainer(NestedWordAutomaton<CodeBlock, String> nwa) {
		mNWA = nwa;
	}

	public NestedWordAutomaton<CodeBlock, String> getNWA() {
		return mNWA;
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		Collection<String> initials = mNWA.getInitialStates();

		ArrayList<NWAVisualizationNode<String, CodeBlock>> visInitials = new ArrayList<>();
		for (String initial : initials) {
			visInitials.add(new NWAVisualizationNode<String, CodeBlock>(mNWA, initial));
		}

		if (visInitials.size() > 1) {
			throw new UnsupportedOperationException();
		} else {
			return new VisualizationNode(visInitials.get(0));
		}
	}

	private class NWAVisualizationNode<NWAVertex, NWAEdge>
			extends
			ModifiableExplicitEdgesMultigraph<NWAVisualizationNode<NWAVertex, NWAEdge>, NWAVisualizationEdge<NWAVertex, NWAEdge>> {

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mBacking == null) ? 0 : mBacking.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			NWAVisualizationNode other = (NWAVisualizationNode) obj;
			if (mBacking == null) {
				if (other.mBacking != null)
					return false;
			} else if (!mBacking.equals(other.mBacking))
				return false;
			return true;
		}

		private final NestedWordAutomaton<NWAEdge, NWAVertex> mVisNWA;
		private final NWAVertex mBacking;
		private static final long serialVersionUID = 1L;
		private boolean mInitialized;

		public NWAVisualizationNode(NestedWordAutomaton<NWAEdge, NWAVertex> nwa, NWAVertex state) {
			super();
			mVisNWA = nwa;
			mBacking = state;
			mInitialized = false;
		}

		@Override
		public List<NWAVisualizationEdge<NWAVertex, NWAEdge>> getOutgoingEdges() {
			if (!mInitialized) {
				for (OutgoingCallTransition<NWAEdge, NWAVertex> succ : mVisNWA.callSuccessors(mBacking)) {
					addOutgoing(new NWAVisualizationEdge<NWAVertex, NWAEdge>(this,
							new NWAVisualizationNode<NWAVertex, NWAEdge>(mVisNWA, succ.getSucc()), succ.getLetter()));
				}
				for (OutgoingInternalTransition<NWAEdge, NWAVertex> succ : mVisNWA.internalSuccessors(mBacking)) {
					addOutgoing(new NWAVisualizationEdge<NWAVertex, NWAEdge>(this,
							new NWAVisualizationNode<NWAVertex, NWAEdge>(mVisNWA, succ.getSucc()), succ.getLetter()));
				}
				for (OutgoingReturnTransition<NWAEdge, NWAVertex> succ : mVisNWA.returnSuccessors(mBacking)) {
					addOutgoing(new NWAVisualizationEdge<NWAVertex, NWAEdge>(this,
							new NWAVisualizationNode<NWAVertex, NWAEdge>(mVisNWA, succ.getSucc()), succ.getLetter()));
				}
				mInitialized = true;
			}
			return super.getOutgoingEdges();
		}

		public String toString() {
			if (mBacking != null) {
				return mBacking.toString();
			}
			return "NULL";
		}

	}

	private class NWAVisualizationEdge<NWAVertex, NWAEdge>
			extends
			ModifiableMultigraphEdge<NWAVisualizationNode<NWAVertex, NWAEdge>, NWAVisualizationEdge<NWAVertex, NWAEdge>> {

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mNWAEdge == null) ? 0 : mNWAEdge.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			NWAVisualizationEdge other = (NWAVisualizationEdge) obj;
			if (mNWAEdge == null) {
				if (other.mNWAEdge != null)
					return false;
			} else if (!mNWAEdge.equals(other.mNWAEdge))
				return false;
			return true;
		}

		private static final long serialVersionUID = 1L;
		private final NWAEdge mNWAEdge;

		protected NWAVisualizationEdge(NWAVisualizationNode<NWAVertex, NWAEdge> source,
				NWAVisualizationNode<NWAVertex, NWAEdge> target, NWAEdge nwaEdge) {
			super(source, target);
			mNWAEdge = nwaEdge;
		}

		@Override
		public String toString() {
			if (mNWAEdge != null) {
				return mNWAEdge.toString();
			}
			return "NULL";
		}
	}
}
