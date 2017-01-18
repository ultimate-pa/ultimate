package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class TreeAST extends AtsASTNode {
	
	private static final long serialVersionUID = -401784715104105435L;

	private final TreeSymbolAST mSymbol;
	private final List<TreeAST> mArguments;
	
	public TreeAST(ILocation loc, TreeSymbolAST sym) {
		super(loc);
		mSymbol = sym;
		mArguments = Collections.emptyList();
		setType(de.uni_freiburg.informatik.ultimate.automata.tree.Tree.class);
	}

	
	public TreeAST(ILocation loc, TreeSymbolAST sym, List<TreeAST> args) {
		super(loc);
		mSymbol = sym;
		mArguments = args;
		setType(de.uni_freiburg.informatik.ultimate.automata.tree.Tree.class);
	}

	public TreeSymbolAST getSymbol() {
		return mSymbol;
	}

	public List<TreeAST> getArguments() {
		return mArguments;
	}
	
	public Tree<String> getTree() {
		
		List<Tree<String>> childTrees = mArguments.stream()
				.map(ta -> ta.getTree())
				.collect(Collectors.toList());

		return new Tree<String>(mSymbol.getAsString(), childTrees);
	}
}
