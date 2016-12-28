/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class VPTfBottomState extends VPTfState {

	public VPTfBottomState(Set<IProgramVar> vars) {
		super(null, null,
				Collections.emptyMap(), Collections.emptyMap(), 
				new HashRelation<>(), 
				Collections.emptySet(),false, vars);
	}

	@Override
	public boolean tracksTerm(Term term) {
		assert false : "check for bottom before calling this! (right?)";
		return super.tracksTerm(term);
	}

	@Override
	public boolean isBottom() {
		return true;
	}

	@Override
	public boolean isTop() {
		return false;
	}

	@Override
	public TransFormula getTransFormula() {
		assert false : "check for bottom before asking for a Transformula";
		return null;
	}

	@Override
	public VPTfArrayIdentifier getArrayIdentifier(Term newArray) {
		assert false : "check for bottom before asking for an ArrayId";
		return null;
	}
	
	@Override
	public String toString() {
		return "VPTfStateBottom " + mVars;
	}
}
