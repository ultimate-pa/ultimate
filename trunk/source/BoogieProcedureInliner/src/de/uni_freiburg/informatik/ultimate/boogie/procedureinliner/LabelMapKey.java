package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

/**
 * Key for the map from old to new label identifiers, used while creating an inline version of a Boogie procedure.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class LabelMapKey {

	private String mLabelId;
	private String mProcedureId;
	private boolean mIsReturnLabel;
	private int mCallNumber;
	
	/**
	 * Creates a new key for a label of the procedure, used as the entry point of inlining.
	 * @param labelId Original identifier of the label.
	 * @param procedureId Identifier of the original procedure, containing the label.
	 */
	public LabelMapKey(String labelId, String procedureId) {
		this(labelId, procedureId, false, 0);
	}

	/**
	 * Creates a new key.
	 * @param labelId Original identifier of the label.
	 * @param procedureId Identifier of the original procedure, containing the label.
	 * @param isReturnLabel The label was created for inlining return statements.
	 * @param callNumber Number of calls to the procedure with identifier {@code procedureId} before the current call.
	 */
	public LabelMapKey(String labelId, String procedureId, boolean isReturnLabel, int callNumber) {
		mLabelId = labelId;
		mProcedureId = procedureId;
		mIsReturnLabel = isReturnLabel;
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

	/** @return The label was created for inlining return statements. */
	public boolean isReturnLabel() {
		return mIsReturnLabel;
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
		result = prime * result + (mIsReturnLabel ? 1231 : 1237);
		result = prime * result + ((mLabelId == null) ? 0 : mLabelId.hashCode());
		result = prime * result + ((mProcedureId == null) ? 0 : mProcedureId.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		LabelMapKey other = (LabelMapKey) obj;
		if (mCallNumber != other.mCallNumber)
			return false;
		if (mIsReturnLabel != other.mIsReturnLabel)
			return false;
		if (mLabelId == null) {
			if (other.mLabelId != null)
				return false;
		} else if (!mLabelId.equals(other.mLabelId))
			return false;
		if (mProcedureId == null) {
			if (other.mProcedureId != null)
				return false;
		} else if (!mProcedureId.equals(other.mProcedureId))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "LabelMapKey [mLabelId=" + mLabelId + ", mProcedureId=" + mProcedureId + ", mIsReturnLabel="
				+ mIsReturnLabel + ", mCallNumber=" + mCallNumber + "]";
	}

}
