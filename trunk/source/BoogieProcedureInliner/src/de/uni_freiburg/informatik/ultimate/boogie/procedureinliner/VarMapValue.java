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
 * Value for the map from old to new variable identifiers, used while creating an inline version of a Boogie procedure.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class VarMapValue {

	private final String mVarId;
	private final DeclarationInformation mDeclInfo;
	
	/**
	 * Creates a new VarMapValue, containing the new identifier and DeclarationInformation of a variable.
	 * @param varId New identifier of the variable.
	 * @param declInfo New DeclarationInformation of the variable.
	 */
	public VarMapValue(String varId, DeclarationInformation declInfo) {
		super();
		mVarId = varId;
		mDeclInfo = declInfo;
	}

	public String getVarId() {
		return mVarId;
	}

	public DeclarationInformation getDeclInfo() {
		return mDeclInfo;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDeclInfo == null) ? 0 : mDeclInfo.hashCode());
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
		final VarMapValue other = (VarMapValue) obj;
		if (mDeclInfo == null) {
			if (other.mDeclInfo != null) {
				return false;
			}
		} else if (!mDeclInfo.equals(other.mDeclInfo)) {
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
		return "VarMapValue [mVarId=" + mVarId + ", mDeclInfo=" + mDeclInfo + "]";
	}
}
