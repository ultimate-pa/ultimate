package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class RankedAlphabetEntryAST extends AtsASTNode {

	String mRank;
	List<String> mAlphabet;

	public RankedAlphabetEntryAST(final ILocation loc, final AtsASTNode rank, final IdentifierListAST alphabet) {
		super(loc);
		mRank = rank.getAsString();
		mAlphabet = alphabet.getIdentifierList();
	}

	public String getRank() {
		return mRank;
	}

	public List<String> getAlphabet() {
		return mAlphabet;
	}

}
