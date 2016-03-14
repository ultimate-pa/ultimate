/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.script;


import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.TreeCache;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.parser.tree.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.tree.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.parser.tree.TreeParser;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedRankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeOps;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTreeCreator;
import de.uni_muenster.cs.sev.lethal.utils.Converter;

/**
 * Hedge (Tree<UnrankedSymbol>) script wrapper class
 * @author Philipp
 *
 */
class HedgeClass extends ScriptClass{
	
	public static final HedgeClass hedgeClass = new HedgeClass();
	
	public HedgeClass() {
		super("Hedge", null, RootClass.newStaticClassEnvironment(), true);
		this.setMember("random", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return new HedgeObject(TreeFactory.getTreeFactory(UnrankedSymbol.class).generateRandomTree(5,10,15));
			}
		});
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		if (args.size() == 1){ //1 Parameter Variant: Tree String given
			if (args.get(0) instanceof StringObject){
				return new HedgeObject(makeTree(((StringObject)args.get(0)).getValue()));
			} else {
				throw new ScriptRuntimeError("Hedge.new expects a String as first parameter");
			}
		} else if (args.size() > 1) { //multi parameter Variant: Root name and subtrees given
			List<Tree<UnrankedSymbol>> subTrees = new ArrayList<Tree<UnrankedSymbol>>();
			for (int i = 1; i < args.size(); i++){
				ScriptObject arg = args.get(i);
				if (arg instanceof StringObject){
					subTrees.add(makeTree(((StringObject)arg).getValue()));
				} else if (arg instanceof HedgeObject){
					subTrees.add(((HedgeObject)arg).getTree());
				} else if (arg instanceof ArrayObject){
					args.addAll(i+1,((ArrayObject)arg).getContent());
				} else {
					throw new ScriptRuntimeError("Hedge.new expects a String, Hedge or Array of Hedge as "+i+" parameter");
				}
			}
			
			if (args.get(0) instanceof StringObject){
				String nodeName = ((StringObject)args.get(0)).getValue();
				try {
					return new HedgeObject(TreeParser.makeHedge(nodeName, subTrees));
				} catch (ParseException e) {
					throw new ScriptRuntimeError("Invalid node name: '" + nodeName + "'");
				}
			} else {
				throw new ScriptRuntimeError("Hedge.new expects a String as first parameter");
			}
		} else {
			throw new ScriptRuntimeError("Hedge.new expects at least 1 parameter");
		}
	}
	
	private Tree<UnrankedSymbol> makeTree(String treeString){
		try {
			return  TreeParser.parseStringAsHedge(treeString);
		} catch (ParseException e) {
			throw new ScriptRuntimeError("Invalid Hedge Term: '" + treeString + "'");
		} catch (TokenMgrError e){
			throw new ScriptRuntimeError("Invalid Hedge Term: '" + treeString + "'");
		}
	}
	
	
}


/**
 * Hedge (Tree<UnrankedSymbol>) script wrapper object
 * @author Philipp
 *
 */
class HedgeObject extends ScriptObject{

	private Tree<UnrankedSymbol> hedge;
	
	public HedgeObject(Tree<UnrankedSymbol> hedge) {
		super(HedgeClass.hedgeClass);
		this.hedge = hedge;
		this.setMember("to_tree", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				Tree<RankedSymbol> tree = TreeOps.convert(
					TreeCache.getTree(HedgeObject.this.hedge),
					new Converter<HedgeSymbol<UnrankedSymbol>, RankedSymbol>(){
						@Override
						public RankedSymbol convert(HedgeSymbol<UnrankedSymbol> a) {
							return new StdNamedRankedSymbol<String>(a.toString(), a.getArity());
						}
					},
					new StdTreeCreator<RankedSymbol>()
				);
				return new TreeObject(tree);
			}
		});
		this.setMember("subtrees", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				List<ScriptObject> subtrees = new ArrayList<ScriptObject>(HedgeObject.this.hedge.getSubTrees().size());
				for (Tree<UnrankedSymbol> subtree : HedgeObject.this.hedge.getSubTrees()){
					subtrees.add(new HedgeObject(subtree));
				}
				return new ArrayObject(subtrees);
			}
		});
		this.setMember("all_symbols", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				Set<UnrankedSymbol> symbols = TreeOps.getAllContainedSymbols(HedgeObject.this.hedge);
				List<ScriptObject> symbolNames = new ArrayList<ScriptObject>(symbols.size());
				for (UnrankedSymbol symbol : symbols){
					symbolNames.add(ScriptObject.make(symbol.toString()));
				}
				return new ArrayObject(symbolNames);
			}
		});
		this.setMember("symbol", ScriptObject.make(hedge.getSymbol().toString()));
		this.setMember("height", ScriptObject.make(TreeOps.getHeight(hedge)));
	}
	
	public Tree<UnrankedSymbol> getTree(){
		return this.hedge;
	}
	
	@Override
	public boolean equals(Object o){
		return (o instanceof HedgeObject) && this.getTree().equals(((HedgeObject)o).getTree());
	}
	
	@Override
	public String toString(){
		return this.hedge.toString();
	}
	
	@Override
	public int hashCode(){
		return this.hedge.hashCode();
	}
}
