package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class TreeAutomatonTransitionAST extends AtsASTNode {
	
	List<String> mSourceStates;
	String mSymbol;
	String mTargetState;

	public TreeAutomatonTransitionAST(ILocation loc, IdentifierListAST sourceStates, String symbol, String targetState) {
		super(loc);
		mSourceStates = sourceStates.getIdentifierList();
		mSymbol = symbol;
		mTargetState = targetState;
	}

}
