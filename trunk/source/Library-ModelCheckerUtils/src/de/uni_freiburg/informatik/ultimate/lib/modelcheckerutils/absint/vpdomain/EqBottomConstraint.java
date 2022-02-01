/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <NODE>
 * @param <FUNCTION>
 */
public class EqBottomConstraint<NODE extends IEqNodeIdentifier<NODE>> extends EqConstraint<NODE> {

	public EqBottomConstraint(final EqConstraintFactory<NODE> factory) {
		super(0, null, null);
	}

	@Override
	public boolean isBottom() {
		return true;
	}

	@Override
	public String toString() {
		return "Bottom";
	}

	@Override
	public Term getTerm(final Script script) {
		return script.term("false");
	}

//	@Override
//	public void freezeAndClose() {
//		// do nothing;
//	}

	@Override
	public boolean isFrozen() {
		return true;
	}

	@Override
	public Set<NODE> getAllNodes() {
		return Collections.emptySet();
	}

//	@Override
//	public void renameVariables(final Map<Term, Term> substitutionMapping) {
//		// do nothing
//	}

	@Override
	public boolean areEqual(final NODE node1, final NODE node2, final boolean addNodesBeforeAnswering) {
		return true;
	}

	@Override
	public boolean areUnequal(final NODE node1, final NODE node2, final boolean addNodesBeforeAnswering) {
		return true;
	}

	@Override
	public Set<IProgramVar> getVariables(final IIcfgSymbolTable symbolTable) {
		return Collections.emptySet();
	}

	@Override
	public Set<IProgramVarOrConst> getPvocs(final IIcfgSymbolTable symbolTable) {
		return Collections.emptySet();
	}

	@Override
	public boolean isTop() {
		return false;
	}

	@Override
	public WeqCongruenceClosure<NODE> getWeqCc() {
		throw new AssertionError("Bottom constraint has no WeqCc");
	}
}
