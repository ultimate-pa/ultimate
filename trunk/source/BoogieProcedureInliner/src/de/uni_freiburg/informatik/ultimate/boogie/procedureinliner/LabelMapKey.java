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

/**
 * Key for the map from old to new label identifiers, used while creating an inline version of a Boogie procedure.
 * A key can also represent a return statement, because they have to be mapped to gotos to a new label.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class LabelMapKey {

	private final String mLabelId;
	private final String mProcedureId;
	private final int mCallNumber;
	
	/**
	 * Creates a new key for a label of the procedure, used inside the entry point of inlining.
	 * @param labelId Original identifier of the label.
	 * @param procedureId Identifier of the original procedure, containing the label.
	 */
	public LabelMapKey(String labelId, String procedureId) {
		this(labelId, procedureId, 0);
	}

	/**
	 * Creates a new key for a label.
	 * @param labelId Original identifier of the label. {@code null} for the generated return label.
	 * @param procedureId Identifier of the original procedure, containing the label.
	 * @param callNumber Number of calls to the procedure with identifier {@code procedureId} before the current call.
	 */
	public LabelMapKey(String labelId, String procedureId, int callNumber) {
		mLabelId = labelId;
		mProcedureId = procedureId;
		mCallNumber = callNumber;
	}
	
	/** @return Original identifier of the label. */
	public String getLabelId() {
		return mLabelId;
	}

	/** @return Identifier of the original procedure, containing the label. */
	public String getProcedureId() {
		return mProcedureId;
	}

	/** @return The label was created for inlining return statements (. */
	public boolean isReturnLabel() {
		return mLabelId == null;
	}

	/** @return Number of calls to the procedure with identifier {@code procedureId} before the current call. */
	public int getCallNumber() {
		return mCallNumber;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + mCallNumber;
		result = prime * result + ((mLabelId == null) ? 0 : mLabelId.hashCode());
		result = prime * result + ((mProcedureId == null) ? 0 : mProcedureId.hashCode());
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
		final LabelMapKey other = (LabelMapKey) obj;
		if (mCallNumber != other.mCallNumber) {
			return false;
		}
		if (mLabelId == null) {
			if (other.mLabelId != null) {
				return false;
			}
		} else if (!mLabelId.equals(other.mLabelId)) {
			return false;
		}
		if (mProcedureId == null) {
			if (other.mProcedureId != null) {
				return false;
			}
		} else if (!mProcedureId.equals(other.mProcedureId)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "LabelMapKey [mLabelId=" + mLabelId + ", mProcedureId=" + mProcedureId + ", mCallNumber=" + mCallNumber
				+ "]";
	}

}
