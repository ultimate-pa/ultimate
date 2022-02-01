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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.VPStatistics;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ITransitionRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class EqTransitionRelation//<ACTION extends IIcfgTransition<IcfgLocation>>
		implements ITransitionRelation {


	private final TransFormula mTf;
	private final EqDisjunctiveConstraint<EqNode> mConstraint;

	public EqTransitionRelation(final EqDisjunctiveConstraint<EqNode> constraint, final TransFormula tf) {
		/*
		 * an EqTransitionRelation inherits all the ITransitionRelation-properties from the TransFormula it was
		 * constructed from (see corresponding getters..)
		 */
		mTf = tf;

		mConstraint = constraint;
	}

	@Override
	public Set<IProgramVar> getAssignedVars() {
		return mTf.getAssignedVars();
	}

	@Override
	public Map<IProgramVar, TermVariable> getInVars() {
		return mTf.getInVars();
	}

	@Override
	public Map<IProgramVar, TermVariable> getOutVars() {
		return mTf.getOutVars();
	}

	@Override
	public Set<IProgramConst> getNonTheoryConsts() {
		return mTf.getNonTheoryConsts();
	}

	@Override
	public boolean isHavocedOut(final IProgramVar bv) {
		return mTf.isHavocedOut(bv);
	}

	@Override
	public boolean isHavocedIn(final IProgramVar bv) {
		return mTf.isHavocedIn(bv);
	}

	@Override
	public Set<TermVariable> getAuxVars() {
		return mTf.getAuxVars();
	}

	public EqDisjunctiveConstraint<EqNode> getEqConstraint() {
		return mConstraint;
	}

	@Override
	public String toString() {
		return "EqTransRel: " + mConstraint.toString();
	}


	public Integer getStatistics(final VPStatistics stat) {
		switch (stat) {
		default :
			return mConstraint.getStatistics(stat);
		}
	}
}
