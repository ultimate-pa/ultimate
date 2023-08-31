package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction.IIndependenceInducedByAbstraction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IndependenceRelationWithAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitSubSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

public class IndependenceInducedByVariableAbstraction<S, L extends IAction>
		implements IIndependenceInducedByAbstraction<S, L, BitSubSet<IProgramVar>> {

	private final VariableAbstraction<L> mAbstraction;
	private final IIndependenceRelation<S, L> mUnderlying;

	public IndependenceInducedByVariableAbstraction(final IIndependenceRelation<S, L> underlying,
			final VariableAbstraction<L> abstraction) {
		mAbstraction = abstraction;
		mUnderlying = underlying;
	}

	@Override
	public IIndependenceRelation<S, L> getInducedIndependence(final BitSubSet<IProgramVar> freeVariables) {
		return new IndependenceRelationWithAbstraction<>(mUnderlying, mAbstraction, freeVariables);
	}

	@Override
	public ILattice<BitSubSet<IProgramVar>> getAbstractionLattice() {
		return mAbstraction.getHierarchy();
	}

}
