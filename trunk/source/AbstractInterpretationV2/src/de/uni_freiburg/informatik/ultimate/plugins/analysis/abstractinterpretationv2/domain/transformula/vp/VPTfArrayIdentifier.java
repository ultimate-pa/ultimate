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

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The VPArrayIdentifier identifies an array occurence inside a TransFormula.
 * Analogously to the VPNodeIdentifier it consists of
 *  - what identifies an array in a VPState --> an IProgramVarOrConst (an EqNode in case of the VPNodeIdentifier)
 *  - inVar and outVar mappings --> here, pairs suffice
 *  
 *  in principle it is possible to reconstruct a term from these, which occurs in the given TransFormula we
 *  created this identifier for.
 *  
 * 
 * @author Alexander Nutz
 */
public class VPTfArrayIdentifier {
	
	IProgramVarOrConst mPvoc;
	Pair<IProgramVar, TermVariable> mInVar;
	Pair<IProgramVar, TermVariable> mOutVar;
	Term mTerm;
	
//	public VPArrayIdentifier(IProgramVarOrConst pvoc) {
//		mPvoc = pvoc;
//	}
	
	public VPTfArrayIdentifier(IProgramVarOrConst pvoc, 
			Pair<IProgramVar, TermVariable> inVar, 
			Pair<IProgramVar, TermVariable> outVar) {
		mPvoc = pvoc;
		
		
		if (inVar != null) {
			mTerm = inVar.getSecond();
		}
		mInVar = inVar;
		
		mOutVar = outVar;
		if (outVar != null) {
			mTerm = outVar.getSecond();
		}
	
		if (mTerm == null) {
			assert pvoc instanceof ConstOrLiteral;
			mTerm = pvoc.getTerm();
		}
	}
	

//	public VPArrayIdentifier(IProgramVarOrConst pvoc, 
//			Map<IProgramVar, TermVariable> inVars, 
//			Map<IProgramVar, TermVariable> outVars) {
//		mPvoc = pvoc;
//		
//		TermVariable iTv = inVars.get(pvoc);
//		if (iTv != null) {
//			mInVar = new Pair<>((IProgramVar) pvoc, iTv);
//			mTerm = iTv;
//		}
//		TermVariable oTv = inVars.get(pvoc);
//		if (oTv != null) {
//			mOutVar = new Pair<>((IProgramVar) pvoc, oTv);
//			mTerm = oTv;
//		}
//		
//		if (mTerm == null) {
//			assert pvoc instanceof ConstOrLiteral;
//			mTerm = pvoc.getTerm();
//		}
//	}

	public VPTfArrayIdentifier(Term term) {
		assert term != null;
		mTerm = term;
	}

//	public VPArrayIdentifier(IProgramVarOrConst function, InOutStatus none) {
//		// TODO Auto-generated constructor stub
//	}

	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VPTfArrayIdentifier)) {
			return false;
		}
		VPTfArrayIdentifier otherArrayId = (VPTfArrayIdentifier) other;
		return this.mTerm == otherArrayId.mTerm 
				&& this.mInVar.equals(otherArrayId.mInVar)
				&& this.mOutVar.equals(otherArrayId.mOutVar)
				&& this.mPvoc == otherArrayId.mPvoc;
	}
	
	@Override
	public String toString() {
		if (mPvoc != null) {
			return "ArrayId: " + mPvoc.toString();
		}
		if (mTerm != null) {
			return "ArrayId: " + mTerm.toString();
		}
		assert false;
		return null;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashHsieh(31, mPvoc, mInVar, mOutVar, mTerm);
	}
	
}
