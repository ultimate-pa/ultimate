package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.independencerelation;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * A simple and efficient syntax-based independence relation.
 * Two actions are independent if all variable accessed by both of them are only read, not written to.
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <STATE> This relation is non-conditional, so this parameter is not used.
 */
public class SyntacticIndependenceRelation<STATE> implements IIndependenceRelation<STATE, IIcfgTransition<?>> {

	@Override
	public boolean isSymmetric() {
		return true;
	}

	@Override
	public boolean isConditional() {
		return false;
	}

	@Override
	public boolean contains(STATE state, IIcfgTransition<?> a, IIcfgTransition<?> b) {
		final TransFormula tf1 = a.getTransformula();
		final TransFormula tf2 = b.getTransformula();

		final boolean noWWConflict = DataStructureUtils.haveEmptyIntersection(tf1.getAssignedVars(),
				tf2.getAssignedVars());
		final boolean noWRConflict = DataStructureUtils.haveEmptyIntersection(tf1.getAssignedVars(),
				tf2.getInVars().keySet());
		final boolean noRWConflict = DataStructureUtils.haveEmptyIntersection(tf1.getInVars().keySet(),
				tf2.getAssignedVars());

		return noWWConflict && noWRConflict && noRWConflict;
	}

}
