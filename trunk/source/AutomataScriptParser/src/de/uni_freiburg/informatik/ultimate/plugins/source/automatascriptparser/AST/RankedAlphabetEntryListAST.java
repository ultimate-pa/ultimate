package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class RankedAlphabetEntryListAST extends AtsASTNode {

	List<RankedAlphabetEntryAST> mList;
	
	public RankedAlphabetEntryListAST(ILocation loc) {
		super(loc);
		mList = new ArrayList<>();
	}

	public void addEntry(RankedAlphabetEntryAST rae) {
		mList.add(rae);
	}

	public List<RankedAlphabetEntryAST> getEntryList() {
		return mList;
	}
}
