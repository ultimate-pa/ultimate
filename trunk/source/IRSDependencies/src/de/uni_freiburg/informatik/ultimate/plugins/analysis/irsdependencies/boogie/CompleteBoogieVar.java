/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.boogie;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

/**
 * Class is used by Daniel for debugging symbol table. Orignially this was
 * a subclass of BoogieVar
 *
 *
 */
public class CompleteBoogieVar
{
	private static final long serialVersionUID = -7848336493120723097L;

	private final String mIdentifier;
	private final String mProcedure;
	private final IBoogieType mIType;
	
	private final boolean mOldvar;
	
	private final int mHashCode;
	
	
	public CompleteBoogieVar(String identifier, String procedure, IBoogieType iType) {
		mIdentifier = identifier;
		mProcedure = procedure;
		mIType = iType;
		mOldvar = false;
		mHashCode = computeHashCode();
	}
	

	
	public String getIdentifier() {
		return mIdentifier;
	}
	
	/**
	 * Returns the procedure in which this variable was declared. If this a 
	 * global variable, then null is returned.
	 */
	public String getProcedure() {
		return mProcedure;
	}
	public IBoogieType getIType() {
		return mIType;
	}
	public boolean isGlobal() {
		return mProcedure == null;
	}
	public boolean isOldvar() {
		return mOldvar;
	}
	


	/**
	 * Returns an identifier that is globally unique. If this is global non-old
	 * we return the identifier, if this is global oldvar we add old(.), if
	 * this is local we add the procedure name as prefix.
	 */
	public String getGloballyUniqueId() {
		if (isGlobal()) {
			if (isOldvar()) {
				return "old(" + mIdentifier+")";
			} else {
				return mIdentifier;
			}
		} else {
			return mProcedure + "_" + mIdentifier;
		}
	}
	
	@Override
	public String toString() {
		return getGloballyUniqueId();
	}

	private int computeHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((mIdentifier == null) ? 0 : mIdentifier.hashCode());
		result = prime * result + (mOldvar ? 1231 : 1237);
		result = prime * result
				+ ((mProcedure == null) ? 0 : mProcedure.hashCode());
		return result;
	}

	@Override
	public int hashCode() {
		return mHashCode;
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
		final CompleteBoogieVar other = (CompleteBoogieVar) obj;
		if (mIdentifier == null) {
			if (other.mIdentifier != null) {
				return false;
			}
		} else if (!mIdentifier.equals(other.mIdentifier)) {
			return false;
		}
		if (mOldvar != other.mOldvar) {
			return false;
		}
		if (mProcedure == null) {
			if (other.mProcedure != null) {
				return false;
			}
		} else if (!mProcedure.equals(other.mProcedure)) {
			return false;
		}
		return true;
	}
	


}
