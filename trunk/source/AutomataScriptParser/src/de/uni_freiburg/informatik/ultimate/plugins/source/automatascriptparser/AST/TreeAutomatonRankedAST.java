package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class TreeAutomatonRankedAST extends AutomatonAST {
	
	private static final long serialVersionUID = -6821752595035882929L;

	//	String mId;
	List<RankedAlphabetEntryAST> mRankedAlphabet;
	List<String> mStates;
	List<String> mFinalStates;
	List<TreeAutomatonTransitionAST> mTransitions;
	
	public TreeAutomatonRankedAST(ILocation loc, String id) {
		super(loc, id);
	}
	

	public void setAlphabet(List<RankedAlphabetEntryAST> entryList) {
		mRankedAlphabet = entryList;
	}

	public void setStates(List<String> identifierList) {
		mStates = identifierList;
	}

	public void setFinalStates(List<String> identifierList) {
		mFinalStates = identifierList;
	}

	public void setTransitions(List<TreeAutomatonTransitionAST> transitions) {
		mTransitions = transitions;
	}

//	public String getmId() {
//		return mId;
//	}

	public List<RankedAlphabetEntryAST> getRankedAlphabet() {
		return mRankedAlphabet;
	}

	public List<String> getStates() {
		return mStates;
	}

	public List<String> getFinalStates() {
		return mFinalStates;
	}

	public List<TreeAutomatonTransitionAST> getTransitions() {
		return mTransitions;
	}


	
}
