/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;

/**
 * Key for the map from old to new variable identifiers, used while creating an inline version of a Boogie procedure.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class VarMapKey {
	
	private final String mVarId;
	private final DeclarationInformation mDeclInfo;
	private final String mInOldExprOfProc;

	/**
	 * Convenience constructor for variables, which didn't appear in (inlined) old() expressions.
	 * @param varId Original identifier of the variable.
	 * @param declInfo Original DeclarationInformation of the variable.
	 */
	public VarMapKey(String varId, DeclarationInformation declInfo) {
		this(varId, declInfo, null);
	}
	
	/**
	 * Creates a new key.
	 * @param varId Original identifier of the variable.
	 * @param declInfo Original DeclarationInformation of the variable.
	 * @param inOldExprOfProc The variable appeared inside an (inlined) old() expression,
	 *                        inside the Procedure with the given identifier.
	 *                        {@code null}, iff the variable wasn't inside an old() expression.
	 */
	public VarMapKey(String varId, DeclarationInformation declInfo, String inOldExprOfProc) {
		mVarId = varId;
		mDeclInfo = declInfo;
		mInOldExprOfProc = inOldExprOfProc;
	}

	/** @return Original identifier of the variable. */
	public String getVarId() {
		return mVarId;
	}

	/** @return Original DeclarationInformation of the variable. */
	public DeclarationInformation getDeclInfo() {
		return mDeclInfo;
	}
	
	/**
	 * @return Identifier of the procedure, in which the variable appeared inside an (inlined) old() expression.
	 *         {@code null}, iff the variable didn't appear in an (inlined) old() expression.
	 */
	public String getInOldExprOfProc() {
		return mInOldExprOfProc;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDeclInfo == null) ? 0 : mDeclInfo.hashCode());
		result = prime * result + ((mInOldExprOfProc == null) ? 0 : mInOldExprOfProc.hashCode());
		result = prime * result + ((mVarId == null) ? 0 : mVarId.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final VarMapKey other = (VarMapKey) obj;
		if (mDeclInfo == null) {
			if (other.mDeclInfo != null) {
				return false;
			}
		} else if (!mDeclInfo.equals(other.mDeclInfo)) {
			return false;
		}
		if (mInOldExprOfProc == null) {
			if (other.mInOldExprOfProc != null) {
				return false;
			}
		} else if (!mInOldExprOfProc.equals(other.mInOldExprOfProc)) {
			return false;
		}
		if (mVarId == null) {
			if (other.mVarId != null) {
				return false;
			}
		} else if (!mVarId.equals(other.mVarId)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "VarMapKey[" + mVarId + " " + mDeclInfo + " " + mInOldExprOfProc + "]";
	}

}
