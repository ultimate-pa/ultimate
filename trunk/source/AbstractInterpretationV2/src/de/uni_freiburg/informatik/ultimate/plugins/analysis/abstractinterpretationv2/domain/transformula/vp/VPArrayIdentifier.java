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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class VPArrayIdentifier {
	
	IProgramVarOrConst mPvoc;
	Term mTerm;
	
//	public VPArrayIdentifier(IProgramVarOrConst pvoc) {
//		mPvoc = pvoc;
//	}

	public VPArrayIdentifier(Term term) {
		assert term != null;
		mTerm = term;
	}

	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VPArrayIdentifier)) {
			return false;
		}
		VPArrayIdentifier otherArrayId = (VPArrayIdentifier) other;
		return this.mTerm == otherArrayId.mTerm && this.mPvoc == otherArrayId.mPvoc;
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
		// TODO
		return 0;
	}
	
}
