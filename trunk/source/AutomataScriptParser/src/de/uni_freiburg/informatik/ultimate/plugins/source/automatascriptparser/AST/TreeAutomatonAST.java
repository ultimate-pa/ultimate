package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class TreeAutomatonAST extends AutomatonAST {
	
//	String mId;
	List<String> mAlphabet;
	List<String> mStates;
	List<String> mInitialStates;
	List<String> mFinalStates;
	List<TreeAutomatonTransitionAST> mTransitions;
	
	public TreeAutomatonAST(ILocation loc, String id) {
		super(loc, id);
	}
	

	public void setAlphabet(List<String> entryList) {
		mAlphabet = entryList;
	}

	public void setStates(List<String> identifierList) {
		mStates = identifierList;
	}

	public void setInitialStates(List<String> identifierList) {
		mInitialStates = identifierList;
	}

	public void setFinalStates(List<String> identifierList) {
		mFinalStates = identifierList;
	}

	public void setTransitions(List<TreeAutomatonTransitionAST> transitions) {
		mTransitions = transitions;
	}

	public List<String> getAlphabet() {
		return mAlphabet;
	}

	public List<String> getStates() {
		return mStates;
	}

	public List<String> getInitialStates() {
		return mInitialStates;
	}

	public List<String> getFinalStates() {
		return mFinalStates;
	}

	public List<TreeAutomatonTransitionAST> getTransitions() {
		return mTransitions;
	}


	
}
