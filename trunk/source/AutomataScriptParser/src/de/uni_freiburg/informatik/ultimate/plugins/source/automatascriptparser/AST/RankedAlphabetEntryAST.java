package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class RankedAlphabetEntryAST extends AtsASTNode {

	String mRank;
	List<String> mAlphabet;

	public RankedAlphabetEntryAST(ILocation loc, String rank, IdentifierListAST alphabet) {
		super(loc);
		mRank = rank;
		mAlphabet = alphabet.getIdentifierList();
	}

}
