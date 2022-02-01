package de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableExplicitEdgesMultigraph;

final class NWAVisualizationNode<NWAVertex, NWAEdge>
		extends
		ModifiableExplicitEdgesMultigraph<NWAVisualizationNode<NWAVertex, NWAEdge>, NWAVisualizationEdge<NWAVertex, NWAEdge>,NWAVertex, NWAEdge> {

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mBacking == null) ? 0 : mBacking.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final NWAVisualizationNode other = (NWAVisualizationNode) obj;
		if (mBacking == null) {
			if (other.mBacking != null) {
				return false;
			}
		} else if (!mBacking.equals(other.mBacking)) {
			return false;
		}
		return true;
	}

	private final INestedWordAutomaton<NWAEdge, NWAVertex> mVisNWA;
	private final NWAVertex mBacking;
	private static final long serialVersionUID = 1L;
	private boolean mInitialized;

	public NWAVisualizationNode(final INestedWordAutomaton<NWAEdge, NWAVertex> nwa, final NWAVertex state) {
		super();
		mVisNWA = nwa;
		mBacking = state;
		mInitialized = false;
	}

	@Override
	public List<NWAVisualizationEdge<NWAVertex, NWAEdge>> getOutgoingEdges() {
		if (!mInitialized) {
			for (final OutgoingCallTransition<NWAEdge, NWAVertex> succ : mVisNWA.callSuccessors(mBacking)) {
				addOutgoing(new NWAVisualizationEdge<NWAVertex, NWAEdge>(this,
						new NWAVisualizationNode<NWAVertex, NWAEdge>(mVisNWA, succ.getSucc()), succ.getLetter()));
			}
			for (final OutgoingInternalTransition<NWAEdge, NWAVertex> succ : mVisNWA.internalSuccessors(mBacking)) {
				addOutgoing(new NWAVisualizationEdge<NWAVertex, NWAEdge>(this,
						new NWAVisualizationNode<NWAVertex, NWAEdge>(mVisNWA, succ.getSucc()), succ.getLetter()));
			}
			for (final OutgoingReturnTransition<NWAEdge, NWAVertex> succ : mVisNWA.returnSuccessors(mBacking)) {
				addOutgoing(new NWAVisualizationEdge<NWAVertex, NWAEdge>(this,
						new NWAVisualizationNode<NWAVertex, NWAEdge>(mVisNWA, succ.getSucc()), succ.getLetter()));
			}
			mInitialized = true;
		}
		return super.getOutgoingEdges();
	}

	@Override
	public String toString() {
		if (mBacking != null) {
			return mBacking.toString();
		}
		return "NULL";
	}

	@Override
	public NWAVertex getLabel() {
		return mBacking;
	}

}