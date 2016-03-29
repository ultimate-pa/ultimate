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
import java.util.List;

import de.uni_muenster.cs.sev.lethal.parser.treetransducer.TreeTransducerParser;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treetransducer.EasyTT;

/**
 * Represents the class of TreeTransducers in the script.
 * @author Philipp
 *
 */
public class TreeTransducerClass extends ScriptClass {

	/** Singleton TreeTransducerClass class instance */
	public static final TreeTransducerClass treeTransducerClass = new TreeTransducerClass();
	
	private TreeTransducerClass() {
		super("TreeTransducer", null, RootClass.newStaticClassEnvironment(), true);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		StringBuilder rulesString = new StringBuilder();
		for (ScriptObject arg : args){
			if (!(arg instanceof StringObject)) throw new ScriptRuntimeError("TreeTransducer.new exptects a String parameter");
			rulesString.append(((StringObject)arg).getValue());
			rulesString.append('\n');
		}
		try {
			return new TreeTransducerObject(TreeTransducerParser.parseString(rulesString.toString()));
		} catch (Exception e) {
			throw new ScriptRuntimeError("Tree Transducer Parser Exception:" + e.getMessage());
		}
	}

}

/**
 * Represents a TreeTransducer in the script
 * @author Philipp
 *
 */
class TreeTransducerObject extends ScriptObject{

	private EasyTT treeTransducer;
	
	public TreeTransducerObject(final EasyTT treeTransducer) {
		super(TreeTransducerClass.treeTransducerClass);
		this.treeTransducer = treeTransducer;
		
		this.setMember("decide", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (!(args.get(0) instanceof TreeObject)) throw new ScriptRuntimeError("TreeTransducer.decide exptect a Tree as parameter");
				Tree<RankedSymbol> tree = ((TreeObject)args.get(0)).getTree();
				return ScriptObject.make(treeTransducer.decide(tree));
			}
		});
		this.setMember("apply", this.setMember("run", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (!(args.get(0) instanceof TreeObject)) throw new ScriptRuntimeError("TreeTransducer.run exptect a Tree as parameter");
				Tree<RankedSymbol> tree = ((TreeObject)args.get(0)).getTree();
				List<ScriptObject> outputTreeObjects = new ArrayList<ScriptObject>(); 
				for (Tree<RankedSymbol> resultTree : treeTransducer.doARun(tree)){
					outputTreeObjects.add(new TreeObject(resultTree));
				}
				
				return new ArrayObject(outputTreeObjects);
			}
		}));
		this.setMember("to_fta", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return new FTAObject(treeTransducer.getFTAPart());
			}
		});
	}
	
	public EasyTT getTreeTransducer(){
		return this.treeTransducer;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TreeTransducerObject other = (TreeTransducerObject) obj;
		if (treeTransducer == null) {
			if (other.treeTransducer != null)
				return false;
		} else if (!treeTransducer.equals(other.treeTransducer))
			return false;
		return true;
	}
	
	@Override
	public String toString(){
		return this.treeTransducer.toString();
	}
}
