package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class TreeAutomatonTransitionListAST extends AtsASTNode {

	
	List<TreeAutomatonTransitionAST> mList;
	
	public TreeAutomatonTransitionListAST(ILocation loc) {
		super(loc);
		mList = new ArrayList<>();
	}

	public void addTransition(TreeAutomatonTransitionAST tat) {
		mList.add(tat);
	}

	public List<TreeAutomatonTransitionAST> getTransitions() {
		return mList;
	}
}
