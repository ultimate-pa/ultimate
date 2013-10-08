package pea_to_boogie.translator;

import de.uni_freiburg.informatik.ultimate.result.Check;

public class ReqCheck extends Check {
	
	private static final long serialVersionUID = 6800618860906443122L;

	enum ReqSpec {
		RTINCONSISTENT,
		VACUOUS,
		INCOMPLETE,
		UNKNOWN
	}
	
	ReqSpec mType;
	int[] mReqNrs;
	Translator mTranslator;
	
	public ReqCheck(ReqSpec type, int[] reqNrs, Translator trans) {
		super(Check.Spec.UNKNOWN);
		this.mType = type;
		this.mReqNrs = reqNrs;
		this.mTranslator = trans;
	}
	
	public int getStartLine() {
		return mReqNrs[0]  + 1;
	}
	public int getEndLine() {
		return mReqNrs[mReqNrs.length-1]  + 1;
	}
	
	public String getPositiveMessage() {
		assert (mType == ReqSpec.RTINCONSISTENT);
		return "Some requirements are rt-consistent";
	}

	public String getNegativeMessage() {
		assert (mType == ReqSpec.RTINCONSISTENT);
		StringBuilder sb = new StringBuilder();
		sb.append("Requirement");
		if (mReqNrs.length != 1)
			sb.append("s");
		for (int nr : mReqNrs) {
			sb.append(" ").append(mTranslator.getRequirement(nr));
		}
		sb.append(" are rt-inconsistent");
		return sb.toString();
	}
	
	public String getFileName() {
		return mTranslator.getInputFilePath();
	}
}
