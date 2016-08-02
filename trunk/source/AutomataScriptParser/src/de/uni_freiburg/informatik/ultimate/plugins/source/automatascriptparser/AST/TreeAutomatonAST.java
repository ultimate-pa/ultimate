package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class TreeAutomatonAST extends AutomatonAST {

	
	String mId;
	
	public TreeAutomatonAST(ILocation loc, String id) {
		super(loc);
		mId = id;
	}

	public void setAlphabet(List<RankedAlphabetEntryAST> entryList) {
		// TODO Auto-generated method stub
	}

	public void setStates(List<String> identifierList) {
		// TODO Auto-generated method stub
		
	}

	public void setFinalStates(List<String> identifierList) {
		// TODO Auto-generated method stub
		
	}

	public void setTransitions(List<TreeAutomatonTransitionAST> transitions) {
		// TODO Auto-generated method stub
		
	}

}
