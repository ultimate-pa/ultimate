package local.stalin.plugins.generator.rcfgbuilder;

public class ReturnAnnot extends TransAnnot {

	private static final long serialVersionUID = 3561826943033450950L;
	
	private final CallAnnot m_CorrespondingCallAnnot;
	
	public ReturnAnnot(CallAnnot callAnnot) {
		m_CorrespondingCallAnnot = callAnnot;
	}
	
	public CallAnnot getCorrespondingCallAnnot() {
		return m_CorrespondingCallAnnot;
	}

}
