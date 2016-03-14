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


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;

import de.uni_muenster.cs.sev.lethal.parser.tree.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.tree.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.parser.tree.TreeParser;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTAOps;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.IdentityConverter;

/**
 * Hedge (Tree<RankedSymbol>) script wrapper class
 * @author Philipp
 *
 */
class TreeClass extends ScriptClass{

	public static final TreeClass treeClass = new TreeClass();
	
	private TreeClass() {
		super("Tree", null, RootClass.newStaticClassEnvironment(), true);
		this.setMember("random", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return new TreeObject(TreeFactory.getTreeFactory(RankedSymbol.class).generateRandomTree(5,10,15));
			}
		});
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		if (args.size() == 1){ //1 Parameter Variant: Tree String given
			if (args.get(0) instanceof StringObject){
				return new TreeObject(makeTree(((StringObject)args.get(0)).getValue()));
			} else {
				throw new ScriptRuntimeError("Tree.new expects a String as first parameter");
			}
		} else if (args.size() > 1) { //multi parameter Variant: Root name and subtrees given
			List<Tree<RankedSymbol>> subTrees = new ArrayList<Tree<RankedSymbol>>();
			for (int i = 1; i < args.size(); i++){
				ScriptObject arg = args.get(i);
				if (arg instanceof StringObject){
					subTrees.add(makeTree(((StringObject)arg).getValue()));
				} else if (arg instanceof TreeObject){
					subTrees.add(((TreeObject)arg).getTree());
				} else if (arg instanceof ArrayObject){
					args.addAll(i+1,((ArrayObject)arg).getContent());
				} else {
					throw new ScriptRuntimeError("Tree.new expects a String, Tree or Array of Trees as "+i+" parameter");
				}
			}
			
			if (args.get(0) instanceof StringObject){
				String nodeName = ((StringObject)args.get(0)).getValue();
				try {
					return new TreeObject(TreeParser.makeTree(nodeName, subTrees));
				} catch (ParseException e) {
					throw new ScriptRuntimeError("Invalid node name: '" + nodeName + "'");
				}
			} else {
				throw new ScriptRuntimeError("Tree.new expects a String as first parameter");
			}
		} else {
			throw new ScriptRuntimeError("Tree.new expects at least 1 parameter");
		}
	}
	
	private Tree<RankedSymbol> makeTree(String treeString){
		try {
			return  TreeParser.parseString(treeString);
		} catch (ParseException e) {
			throw new ScriptRuntimeError("Invalid Tree Term: '" + treeString + "'");
		} catch (TokenMgrError e){
			throw new ScriptRuntimeError("Invalid Tree Term: '" + treeString + "'");
		}
	}
	
	
}

/**
 * Tree (Tree<RankedSymbol>) script wrapper object
 * @author Philipp
 *
 */
class TreeObject extends ScriptObject{

	private Tree<RankedSymbol> tree;
	
	public TreeObject(Tree<RankedSymbol> tree) {
		super(TreeClass.treeClass);
		this.tree = tree;
		this.setMember("singleton_fta", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				EasyFTA automaton;
				automaton = EasyFTAOps.computeSingletonFTA(TreeObject.this.tree);
				final HashMap<State,State> stateMap = new HashMap<State,State>(); 
				automaton = FTAOps.ftaConverter(automaton, new Converter<State,State>(){
					@Override
					public State convert(State a) {
						State q = stateMap.get(a);
						if (q == null) {q = StateFactory.getStateFactory().makeState(); stateMap.put(a,q);}
						return q;
					}
				}, new IdentityConverter<RankedSymbol>(), new EasyFTACreator());
				return new FTAObject(automaton);
			}
			
		});
		this.setMember("subtrees", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				List<ScriptObject> subtrees = new ArrayList<ScriptObject>(TreeObject.this.tree.getSubTrees().size());
				for (Tree<RankedSymbol> subtree : TreeObject.this.tree.getSubTrees()){
					subtrees.add(new TreeObject(subtree));
				}
				return new ArrayObject(subtrees);
			}
		});
		this.setMember("all_symbols", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				Set<RankedSymbol> symbols = TreeOps.getAllContainedSymbols(TreeObject.this.tree);
				List<ScriptObject> symbolNames = new ArrayList<ScriptObject>(symbols.size());
				for (RankedSymbol symbol : symbols){
					symbolNames.add(ScriptObject.make(symbol.toString()));
				}
				return new ArrayObject(symbolNames);
			}
		});
		
		this.setMember("symbol", ScriptObject.make(tree.getSymbol().toString()));
		this.setMember("height", ScriptObject.make(TreeOps.getHeight(tree)));
	}
	
	public Tree<RankedSymbol> getTree(){
		return this.tree;
	}
	
	@Override
	public boolean equals(Object o){
		return (o instanceof TreeObject) && this.getTree().equals(((TreeObject)o).getTree());
	}
	
	@Override
	public String toString(){
		return this.tree.toString();
	}
	
	@Override
	public int hashCode(){
		return this.tree.hashCode();
	}
}
