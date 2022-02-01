/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class TreeAST extends AtsASTNode {

	private static final long serialVersionUID = -401784715104105435L;

	private final TreeSymbolAST mSymbol;
	private final List<TreeAST> mArguments;

	public TreeAST(final ILocation loc, final TreeSymbolAST sym) {
		super(loc);
		mSymbol = sym;
		mArguments = Collections.emptyList();
		setType(de.uni_freiburg.informatik.ultimate.automata.tree.Tree.class);
	}

	public TreeAST(final ILocation loc, final TreeSymbolAST sym, final List<TreeAST> args) {
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

	public Tree<StringRankedLetter> getTree() {
		final List<Tree<StringRankedLetter>> childTrees = 
				mArguments.stream().map(ta -> ta.getTree()).collect(Collectors.toList());
		return new Tree<>(new StringRankedLetter(mSymbol.toString(), childTrees.size()), childTrees);
	}
	
	@Override
	public String getAsString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(mSymbol.toString());

		if (!mArguments.isEmpty()) {
			sb.append("(");
		}
		String sep = "";
		for (TreeAST arg : mArguments) {
			sb.append(sep);
			sb.append(arg.getAsString());
			sep = ", ";
		}
		if (!mArguments.isEmpty()) {
			sb.append(")");
		}
		
		
		return sb.toString();
		
//		return getTree().toString();
	}
}
