package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class TreeAutomatonAST extends AutomatonAST {

	
	String mId;
	
	public TreeAutomatonAST(ILocation loc, String id) {
		super(loc);
		mId = id;
	}

}
