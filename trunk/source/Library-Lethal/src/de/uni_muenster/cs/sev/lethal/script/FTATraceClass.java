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
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;

/**
 * Class for FTATraces.
 * A FTATrace packages the result of AbstractModeFTA.annotateWithStates(tree) together with the FTA and Tree it was run on.
 * This allows to display the result of annotateWithStates with the show() command
 * 
 * @author Philipp
 *
 */
public class FTATraceClass extends ScriptClass {

	/** Singleton FTATraceClass class instance */
	public static final FTATraceClass ftaTraceClass = new FTATraceClass();
	
	private FTATraceClass() {
		super("FTATrace", null, RootClass.newStaticClassEnvironment(), false);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		return null;
	}

}

/**
 * Object for FTATraces.
 * A FTATrace packages the result of AbstractModeFTA.annotateWithStates(tree) together with the FTA and Tree it was run on.
 * This allows to display the result of annotateWithStates with the show() command
 *
 * @author Philipp
 *
 */
class FTATraceObject extends ScriptObject{

	private TreeObject tree;
	private FTAObject fta;
	private Map<Tree<RankedSymbol>,Set<FTARule<RankedSymbol,State>>> tracemap;
	
	public FTATraceObject(TreeObject tree, FTAObject fta, Map<Tree<RankedSymbol>, Set<FTARule<RankedSymbol,State>>> tracemap) {
		super(FTATraceClass.ftaTraceClass);
		this.tree = tree;
		this.fta = fta;
		this.tracemap = tracemap;
		
		HashMap<ScriptObject,ScriptObject> stracemap = new HashMap<ScriptObject,ScriptObject>();
		
		for (Tree<RankedSymbol> key : tracemap.keySet()){
			TreeObject skey = new TreeObject(key);
			List<ScriptObject> value = new ArrayList<ScriptObject>();
			for (FTARule<RankedSymbol,State> rule : tracemap.get(key)){
				value.add(ScriptObject.make(rule.toString()));
			}
			ArrayObject svalue = new ArrayObject(value);
			stracemap.put(skey,svalue);
		}
		
		this.setMember("tree", tree);
		this.setMember("fta",  fta);
		this.setMember("tracemap", new HashObject(stracemap));
	}
	
	public Tree<RankedSymbol> getTree(){
		return this.tree.getTree();
	}
	
	public FTA<RankedSymbol, State, ? extends FTARule<RankedSymbol,State>> getFTA(){
		return this.fta.getAutomaton();
	}
	
	public Map<Tree<RankedSymbol>,Set<FTARule<RankedSymbol,State>>> getTracemap(){
		return this.tracemap;
	}
	
	
	@Override
	public String toString(){
		return "Trace(" + this.tree.toString() + ", " + this.tracemap.toString() + ")";
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof FTATraceObject)) return false;
		return ((FTATraceObject)o).tree.equals(this.tree) && ((FTATraceObject)o).tracemap.equals(this.tracemap);
	}
	
	@Override
	public int hashCode(){
		return this.tree.hashCode() + 31*this.tracemap.hashCode();
	}
}
