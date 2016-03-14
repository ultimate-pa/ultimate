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

import de.uni_muenster.cs.sev.lethal.gui.Project;
import de.uni_muenster.cs.sev.lethal.gui.TreeAutomatonDisplayWindow;
import de.uni_muenster.cs.sev.lethal.gui.TreeDisplayWindow;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.EasyHedgeAutomaton;

import java.io.PrintStream;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;

/**
 * Script interpreter root class containing the "global" function bindings, all object environments root here.
 * @author Philipp
 *
 */
class RootClass extends ScriptClass{

	public static final Environment rootEnv = new Environment(null);
	public static final RootClass rootClass = new RootClass();
	
	private RootClass() {
		super("Root", null, rootEnv, false);
		Environment env = this.getEnvironment();
		env.bindLocal("exp"    , new ExpMethod());
		env.bindLocal("sqrt"   , new SqrtMethod());
		env.bindLocal("PI"     , new FloatObject(Math.PI));
		env.bindLocal("E"      , new FloatObject(Math.E));

		env.bindLocal("Integer", IntegerClass.integerClass);
		env.bindLocal("Float"  , FloatClass.floatClass);
		env.bindLocal("String" , StringClass.stringClass);
		env.bindLocal("Boolean", BooleanClass.booleanClass);
		
		env.bindLocal("Array"  , ArrayClass.arrayClass);
		env.bindLocal("Hash"   , HashClass.hashClass);
		env.bindLocal("Range"  , RangeClass.rangeClass);
		
		env.bindLocal("Tree",           TreeClass.treeClass);
		env.bindLocal("FTA" ,           FTAClass.ftaClass);
		env.bindLocal("Homomorphism",   HomomorphismClass.homClass);
		env.bindLocal("TreeTransducer", TreeTransducerClass.treeTransducerClass);
		env.bindLocal("Hedge",          HedgeClass.hedgeClass);
		env.bindLocal("HedgeAutomaton", HAClass.haClass);
		env.bindLocal("HA"            , HAClass.haClass);
		env.bindLocal("FTATrace",       FTATraceClass.ftaTraceClass);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		throw new UnsupportedOperationException("Cannot create an instance of the script root class");
	}
	
	/**
	 * Creates a new environment for static classes (classes that are the same for all scripts running)
	 * @return the new environment
	 */
	public static Environment newStaticClassEnvironment(){
		return rootEnv.newFrame();
	}
	
}

class RootObject extends ScriptObject{

	public RootObject(PrintStream outputStream, Project project) {
		super(RootClass.rootClass);
		this.setMember("print"  , new PrintMethod(outputStream));
		if (project != null) this.setMember("show"   , new ShowMethod(project));
	}
	
}




/**
 * Buildin method for console output
 * @author Philipp
 *
 */
class PrintMethod extends Method {

	private PrintStream out;
	
	public PrintMethod(PrintStream out) {
		super(ARITY_ARBITARY);
		this.out = out;
	}

	@Override
	public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
		for (ScriptObject arg : args){
			this.out.print(arg.toString());
		}
		this.out.println();
		return ScriptObject.nullValue;
	}
	
	public void setOutputStream(PrintStream out){
		this.out = out;
	}
	
}

class ShowMethod extends Method{

	private Project project;
	
	ShowMethod(Project project){
		super(ARITY_ONE_OR_TWO);
		this.project = project;
	}
	
	@Override
	public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
		String title = null;
		if (args.size() == 2){
			if (!(args.get(1) instanceof StringObject)) throw new ScriptRuntimeError("show(tree|fta [,title]) expects a string argument as second parameter");
			title = ((StringObject)args.get(1)).getValue();
		}
		
		if ((args.get(0) instanceof TreeObject)){ 
			Tree<RankedSymbol> tree = ((TreeObject)args.get(0)).getTree();
			new TreeDisplayWindow(tree, this.project, title, null, null, title);
		} else if ((args.get(0) instanceof HedgeObject)){ 
			Tree<UnrankedSymbol> hedge = ((HedgeObject)args.get(0)).getTree();
			new TreeDisplayWindow(hedge, this.project, title, null, null, title);
		} else if ((args.get(0) instanceof FTAObject)){ 
			EasyFTA fta = ((FTAObject)args.get(0)).getAutomaton();
			new TreeAutomatonDisplayWindow(fta, this.project, title, null, title);
		} else if ((args.get(0) instanceof HAObject)){ 
			EasyHedgeAutomaton ha = ((HAObject)args.get(0)).getAutomaton();
			new TreeAutomatonDisplayWindow(ha, this.project, title, null, title);
		} else if ((args.get(0) instanceof FTATraceObject)){
		    Tree<RankedSymbol> tree = ((FTATraceObject)args.get(0)).getTree();
			Map<Tree<RankedSymbol>, Set<FTARule<RankedSymbol,State>>> tracemap = ((FTATraceObject)args.get(0)).getTracemap();
			FTA<RankedSymbol, State, ? extends FTARule<RankedSymbol,State>> fta = ((FTATraceObject)args.get(0)).getFTA();
			new TreeDisplayWindow(tree, null, null, fta.getFinalStates(), tracemap, title);	
		} else {
			throw new ScriptRuntimeError("show(tree|fta [,title]) expects a tree, fta or ftatrace argument as first parameter");
		}
		
		return ScriptObject.nullValue;
	}
	
}

/**
 * Buildin method for exp(x) (raise e to the power of x)
 * @author Philipp
 */
class ExpMethod extends Method {

	public ExpMethod() {
		super(1);
	}

	@Override
	public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
		ScriptObject val = args.get(0);
		if (val instanceof FloatObject) {
			return new FloatObject(Math.exp(((FloatObject) val).getValue()));
		} else if (val instanceof IntegerObject){
			return new FloatObject(Math.exp(((IntegerObject) val).getValue()));
		} else {
			throw new ScriptRuntimeError("exp() expects numeric argument");
		}
	}
}

/**
 * Buildin method for sqrt(x) (square root of x)
 * @author Philipp
 */
class SqrtMethod extends Method {

	public SqrtMethod() {
		super(1);
	}

	@Override
	public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
		ScriptObject val = args.get(0);
		if (val instanceof FloatObject) {
			return new FloatObject(Math.sqrt(((FloatObject) val).getValue()));
		} else if (val instanceof IntegerObject){
			return new FloatObject(Math.sqrt(((IntegerObject) val).getValue()));
		} else {
			throw new ScriptRuntimeError("sqrt() expects numeric argument");
		}
	}
	
}
