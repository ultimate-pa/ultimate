/*
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
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
	public boolean contains(final STATE state, final IIcfgTransition<?> a, final IIcfgTransition<?> b) {
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
