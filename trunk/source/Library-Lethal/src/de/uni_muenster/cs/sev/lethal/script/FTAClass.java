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
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;

import de.uni_muenster.cs.sev.lethal.parser.fta.FTAParser;
import de.uni_muenster.cs.sev.lethal.parser.fta.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.fta.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedRankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTAOps;
import de.uni_muenster.cs.sev.lethal.utils.*;

/**
 * Class for creating new Finite Tree Automatons
 * Usage is FTA.new(rule1,rule2,...) where ruleX must be valid rule strings. @see FTAParser
 * @author Philipp
 */
public class FTAClass extends ScriptClass{
	
	/** Singleton FTAClass class instance */
	public static final FTAClass ftaClass = new FTAClass();
	
	/**
	 * Create the FTAClass. To be done once by script interpreter initialization.
	 * @param classEnvironment environment for this class
	 */
	private FTAClass() {
		super("FTA", null, RootClass.newStaticClassEnvironment(), true);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		List<String> ruleStrings = new ArrayList<String>();
		for (ScriptObject arg : args){
			if (!(arg instanceof StringObject)) throw new ScriptRuntimeError("FTA.new exptects a String parameter");
			ruleStrings.add(((StringObject)arg).getValue());
		}
		try {
			return new FTAObject(FTAParser.parseStrings(ruleStrings));
		} catch (TokenMgrError e) {
			throw new ScriptRuntimeError(e.getMessage());
		} catch (ParseException e) {
			throw new ScriptRuntimeError(e.getMessage());
		}
	}

}

/**
 * FTA Wrapper object. Encapsulates an FiniteTreeAutomaton object and exposes TreeAutomataOperations methods as script methods
 * @author Philipp
 *
 */
class FTAObject extends ScriptObject{

	private EasyFTA automaton;
	
	/**
	 * Create a new FTAObject
	 * @param automaton FTA be contained by this FTAObject
	 */
	protected FTAObject(EasyFTA automaton) {
		super(FTAClass.ftaClass);
		this.automaton = automaton;
		this.setMember("decide", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof TreeObject)) throw new ScriptRuntimeError("FTA.decide expects Tree as argument");
				TreeObject t = (TreeObject)args.get(0);
				return ScriptObject.make(FTAObject.this.automaton.decide(t.getTree()));
			}
		});
		
		this.setMember("trace", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof TreeObject)) throw new ScriptRuntimeError("FTA.trace expects Tree as argument");
				TreeObject t = (TreeObject)args.get(0);

				Map<Tree<RankedSymbol>,Set<FTARule<RankedSymbol,State>>> tracemap = FTAOps.annotateTreeWithRules(FTAObject.this.automaton,t.getTree());
				
				return new FTATraceObject(t, (FTAObject)env.getThis(), tracemap);
			}
		});
		
		this.setMember("*", this.setMember("intersect", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof FTAObject)) throw new ScriptRuntimeError("FTA.intersect expects FTA as argument");
				FTAObject t = (FTAObject)args.get(0);
				return new FTAObject(EasyFTAOps.intersectionTD(FTAObject.this.automaton, t.automaton));
			}
		}));
		this.setMember("+", this.setMember("union", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof FTAObject)) throw new ScriptRuntimeError("FTA.union expects FTA as argument");
				FTAObject t = (FTAObject)args.get(0);
				return new FTAObject(EasyFTAOps.union(FTAObject.this.automaton, t.automaton));
			}
		}));
		this.setMember("-", this.setMember("subtract", this.setMember("difference", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof FTAObject)) throw new ScriptRuntimeError("FTA.union expects FTA as argument");
				FTAObject t = (FTAObject)args.get(0);
				return new FTAObject(EasyFTAOps.difference(FTAObject.this.automaton, t.automaton));
			}
		})));
		
		this.setMember("reduce_bottom_up", this.setMember("reduce", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return new FTAObject(EasyFTAOps.reduceBottomUp(FTAObject.this.automaton));
			}
		}));
		this.setMember("reduce_top_down", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return new FTAObject(EasyFTAOps.reduceTopDown(FTAObject.this.automaton));
			}
		});
		this.setMember("reduce_full", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return new FTAObject(EasyFTAOps.reduceFull(FTAObject.this.automaton));
			}
		});
		this.setMember("minimize", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (args.size() != 0) throw new ScriptRuntimeError("FTA.minimize takes no parameters");
				return new FTAObject(EasyFTAOps.minimize(FTAObject.this.automaton));
			}
		});
		/*this.setMember("complement", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (!(args.get(0) instanceof ArrayObject)) throw new ScriptRuntimeError("FTA.complement(alphabet) expects Array argument");
				Set<RankedSymbol> alphabet = new HashSet<RankedSymbol>();
				for (ScriptObject obj : ((ArrayObject)args.get(0)).getContent()){
					alphabet.add(new StdNamedRankedSymbol<String>(obj.toString(), airty ));
				}
				return new FTAObject(EasyFTAOps.complementAlphabet(FTAObject.this.automaton, alphabet));
			}
		});*/
		this.setMember("complete", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (args.size() != 0) throw new ScriptRuntimeError("FTA.complete takes no parameters");
				return new FTAObject(EasyFTAOps.complete(FTAObject.this.automaton));
			}
		});
		this.setMember("determinize", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (args.size() != 0) throw new ScriptRuntimeError("FTA.determinize takes no parameters");
				return new FTAObject(EasyFTAOps.determinize(FTAObject.this.automaton));
			}
		});
		this.setMember("empty_language", this.setMember("emptyLanguage", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(FTAProperties.emptyLanguage(FTAObject.this.automaton));
			}
		}));
		this.setMember("finite_language", this.setMember("finiteLanguage", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(FTAProperties.finiteLanguage(FTAObject.this.automaton));
			}
		}));
		this.setMember("is_deterministic", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(FTAProperties.checkDeterministic(FTAObject.this.automaton));
			}
		});
		this.setMember("is_complete", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(FTAProperties.checkComplete(FTAObject.this.automaton));
			}
		});
		
		this.setMember("==",this.setMember("same_language", this.setMember("sameLanguage", this.setMember("sameLanguageAs", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof FTAObject)) throw new ScriptRuntimeError("FTA.sameLanguageAs? expects FTA as argument");
				FTAObject t = (FTAObject)args.get(0);
				return ScriptObject.make(FTAProperties.sameLanguage(FTAObject.this.automaton, t.automaton));
			}
		}))));
		this.setMember("<=", this.setMember("subset_language", this.setMember("subsetLanguage", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof FTAObject)) throw new ScriptRuntimeError("FTA.subsetLanguage expects FTA as argument");
				FTAObject t = (FTAObject)args.get(0);
				return ScriptObject.make(FTAProperties.subsetLanguage(FTAObject.this.automaton, t.automaton));
			}
		})));
		this.setMember("<", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof FTAObject)) throw new ScriptRuntimeError("< on FTA expects FTA as argument");
				FTAObject t = (FTAObject)args.get(0);
				return ScriptObject.make(FTAProperties.subsetLanguage(FTAObject.this.automaton, t.automaton) && !FTAProperties.subsetLanguage(t.automaton, FTAObject.this.automaton));
			}
		});

		
		this.setMember("example_tree", this.setMember("exampleTree", new Method(Method.ARITY_ZERO_OR_ONE){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				 Tree<RankedSymbol> tree;
				 if (args.size() == 0){
					 tree = EasyFTAOps.constructTreeFrom(FTAObject.this.automaton);
				 } else {
					 if (!(args.get(0) instanceof IntegerObject)) throw new ScriptRuntimeError("FTA.example_tree() expectes none or Integer argument");
					 int minHeight = ((IntegerObject)args.get(0)).getValue(); 
					 tree = EasyFTAOps.constructTreeWithMinHeightFrom(FTAObject.this.automaton, minHeight, false);
				 }
				 return tree == null ? ScriptObject.nullValue : new TreeObject(tree);
			}
		}));
		
		this.setMember("rename_states", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, final MethodObject block) {
				if (block == null) throw new ScriptRuntimeError("rename_states requires a block");
				final List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1);
				blockArgs.add(null);
				
				EasyFTA fta = FTAOps.ftaConverter(FTAObject.this.automaton,
					new CachedConverter<State,State>(){
						@Override
						public State uniqueConvert(State a) {
							blockArgs.set(0, ScriptObject.make(a.toString()));
							return StateFactory.getStateFactory().makeState(block.call(blockArgs, null).toString()); 
						}
					}, new IdentityConverter<RankedSymbol>(), new EasyFTACreator());
				return new FTAObject(fta);
			}
		});
		this.setMember("rename_symbols", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, final MethodObject block) {
				if (block == null) throw new ScriptRuntimeError("rename_symbols requires a block");
				
				final List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(2);
				blockArgs.add(null);
				blockArgs.add(null);
				
				EasyFTA fta = FTAOps.ftaConverter(FTAObject.this.automaton,
					new IdentityConverter<State>(),
					new CachedConverter<RankedSymbol,RankedSymbol>(){
					@Override
					public RankedSymbol uniqueConvert(RankedSymbol s) {
						blockArgs.set(0, ScriptObject.make(s.toString()));
						blockArgs.set(1, ScriptObject.make(s.getArity()));
						return new StdNamedRankedSymbol<String>(block.call(blockArgs, null).toString(), s.getArity()); 
					}
				}, new EasyFTACreator());
				return new FTAObject(fta);
			}
		});
		
		List<ScriptObject> states = new ArrayList<ScriptObject>(this.automaton.getStates().size());
		for (State state : (Set<? extends State>)this.automaton.getStates()){
			states.add(ScriptObject.make(state.toString()));
		}
		this.setMember("states", new ArrayObject(states));
		List<ScriptObject> finalstates = new ArrayList<ScriptObject>(this.automaton.getStates().size());
		for (State state : (Set<? extends State>)this.automaton.getFinalStates()){
			finalstates.add(ScriptObject.make(state.toString()));
		}
		this.setMember("final_states", new ArrayObject(states));

		
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof FTAObject)) return false;
		return FTAProperties.sameLanguage(((FTAObject)o).getAutomaton(), this.automaton);
	}
	
	@Override
	public String toString(){
		return this.automaton.toString();
	}
	
	public EasyFTA getAutomaton(){
		return this.automaton;
	}
	
	@Override
	public int hashCode(){
		return this.automaton.hashCode();
	}
}
