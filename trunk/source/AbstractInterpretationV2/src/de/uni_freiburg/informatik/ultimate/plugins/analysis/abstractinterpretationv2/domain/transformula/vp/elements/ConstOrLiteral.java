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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class ConstOrLiteral implements IProgramVarOrConst {
	
	final bvocType mType;
	
	final Term mTerm;
	
	final ConstantTerm mConstantTerm;

	final ApplicationTerm mApplicationTerm;
	
	final BoogieConst mBoogieConst;
	
	// TODO: could BoogieConst be moved out here (like IProgramVar before??)
	public ConstOrLiteral(BoogieConst bc) {
		assert false : "not used, right??";
		mType = bvocType.BOOGIECONST;
		mTerm = bc.getTerm();
		mConstantTerm = null;
		mBoogieConst = bc;
		mApplicationTerm = null;
	}
	
	public ConstOrLiteral(ApplicationTerm at) {
		mType = bvocType.APPLICATIONTERMLITERAL;
		mTerm = at;
		mConstantTerm = null;
		mBoogieConst = null;
		mApplicationTerm = at;
	}

	public ConstOrLiteral(ConstantTerm ct) {
		mType = bvocType.CONSTANTTERMLITERAL;
		mTerm = ct;
		mConstantTerm = ct;
		mBoogieConst = null;
		mApplicationTerm = null;
	}
	
	@Override
	public String getGloballyUniqueId() {
		switch (mType) {
		case BOOGIECONST:
			return mBoogieConst.getGloballyUniqueId();
		case CONSTANTTERMLITERAL:
			return mConstantTerm.toString();
		case APPLICATIONTERMLITERAL:
			return mApplicationTerm.toString();
		default:
			assert false;
			return null;
		}
	}

	@Override
	public Term getTerm() {
		return mTerm;
	}
	
	@Override
	public String toString() {
		return mTerm.toString();
	}
	
	@Override
	public boolean isGlobal() {
		if (mType == bvocType.CONSTANTTERMLITERAL) {
			return true;
		} else if (mType == bvocType.APPLICATIONTERMLITERAL) {
			return true;
		} else {
			assert mType == bvocType.BOOGIECONST;
			return mBoogieConst.isGlobal();
		} 
	}
	
	private enum bvocType { BOOGIECONST, APPLICATIONTERMLITERAL, CONSTANTTERMLITERAL };
}
