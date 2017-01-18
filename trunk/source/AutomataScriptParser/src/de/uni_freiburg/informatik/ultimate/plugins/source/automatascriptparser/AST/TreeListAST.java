package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class TreeListAST extends AtsASTNode {

	private static final long serialVersionUID = -8975478484794688588L;

	private final List<TreeAST> mList;
	
	
	public TreeListAST(ILocation loc) {
		super(loc);
		mList = new ArrayList<TreeAST>();
	}
	
	public TreeListAST(ILocation loc, TreeAST firstSym) {
		super(loc);
		mList = new ArrayList<TreeAST>();
		mList.add(firstSym);
	}

	
	public void add(TreeAST ts) {
		mList.add(ts);
	}
	
	public List<TreeAST> getList() {
		return mList;
	}
	
}
