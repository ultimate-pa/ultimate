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


import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.EasyHAOps;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.EasyHedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HAOps;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.HedgeAutomatonParser;
import de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedRankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedUnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTACreator;
import de.uni_muenster.cs.sev.lethal.utils.Converter;

/**
 * Class for creating new Finite Tree Automatons
 * Usage is HedgeAutomaton.new(rule1,rule2,...) where ruleX must be valid rule strings. @see HedgeAutomatonParser
 * @author Philipp
 */
public class HAClass extends ScriptClass{
	
	/** Singleton HAClass class instance */
	public static final HAClass haClass = new HAClass();
	
	private HAClass() {
		super("HedgeAutomaton", null, RootClass.newStaticClassEnvironment(), true);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		StringBuffer rulesString = new StringBuffer();
		for (ScriptObject arg : args){
			if (!(arg instanceof StringObject)) throw new ScriptRuntimeError("HedgeAutomaton.new exptects a String parameter");
			rulesString.append(((StringObject)arg).getValue());
			rulesString.append('\n');
		}
		try {
			return new HAObject(HedgeAutomatonParser.parseString(rulesString.toString()));
		} catch (TokenMgrError e) {
			throw new ScriptRuntimeError(e.getMessage());
		} catch (ParseException e) {
			throw new ScriptRuntimeError(e.getMessage());
		}
	}
}	

/**
 * HedgeAutomaton Wrapper object. Encapsulates a HedgeAutomaton object and exposes HAOps Operations methods as script methods
 * @author Philipp
 *
 */
class HAObject extends ScriptObject{

	private EasyHedgeAutomaton automaton;
	
	public HAObject(EasyHedgeAutomaton automaton) {
		super(HAClass.haClass);
		this.automaton = automaton;
		
		this.setMember("decide", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof HedgeObject)) throw new ScriptRuntimeError("HedgeAutomaton.decide expects Hedge as argument");
				HedgeObject t = (HedgeObject)args.get(0);
				return ScriptObject.make(HAOps.decide(HAObject.this.automaton, t.getTree()));
			}
		});
		
		/*this.setMember("trace", new Method(){
			@Override
			public ScriptObject invoke(ScriptObject object, List<ScriptObject> args, Method block) {
				if (! (args.get(0) instanceof TreeObject)) throw new ScriptRuntimeError("HedgeAutomaton.trace expects Tree as argument");
				TreeObject t = (TreeObject)args.get(0);

				Map<Hedge<RankedSymbol>,Set<State>> tracemap = ((HAObject)object).getAutomaton().annotateTreeWithStates(t.getTree());
				
				return new FTATraceObject((ScriptClass)(object.getEnvironment().get("FTATrace")), t, (HAObject)object, tracemap);
			}
		});*/
		this.setMember("complement", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (!(args.get(0) instanceof ArrayObject)) throw new ScriptRuntimeError("HedgeAutomaton.complement(alphabet) expects Array argument");
				Set<UnrankedSymbol> alphabet = new HashSet<UnrankedSymbol>();
				for (ScriptObject obj : ((ArrayObject)args.get(0)).getContent()){
					alphabet.add(new StdNamedUnrankedSymbol<String>(obj.toString()));
				}
				return new HAObject(EasyHAOps.complementAlphabet(HAObject.this.automaton, alphabet));
			}
		});
		this.setMember("*", this.setMember("intersect", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof HAObject)) throw new ScriptRuntimeError("HedgeAutomaton.intersect expects HedgeAutomaton as argument");
				HAObject t = (HAObject)args.get(0);
				return new HAObject(EasyHAOps.intersection(HAObject.this.automaton, t.automaton));
			}
		}));
		this.setMember("+", this.setMember("union", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof HAObject)) throw new ScriptRuntimeError("HedgeAutomaton.union expects HedgeAutomaton as argument");
				HAObject t = (HAObject)args.get(0);
				return new HAObject(EasyHAOps.union(HAObject.this.automaton, t.automaton));
			}
		}));
		this.setMember("-", this.setMember("subtract", this.setMember("difference", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof HAObject)) throw new ScriptRuntimeError("HedgeAutomaton.difference expects HedgeAutomaton as argument");
				HAObject t = (HAObject)args.get(0);
				return new HAObject(EasyHAOps.difference(HAObject.this.automaton, t.automaton));
			}
		})));
		this.setMember("empty_language", this.setMember("emptyLanguage", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(HAOps.emptyLanguage(HAObject.this.automaton));
			}
		}));
		this.setMember("finite_language", this.setMember("finiteLanguage", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(HAOps.finiteLanguage(HAObject.this.automaton));
			}
		}));
		this.setMember("==", this.setMember("same_language", this.setMember("sameLanguage", this.setMember("sameLanguageAs", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof HAObject)) throw new ScriptRuntimeError("HedgeAutomaton.same_language expects HedgeAutomaton as argument");
				HAObject t = (HAObject)args.get(0);
				return ScriptObject.make(HAOps.sameLanguage(HAObject.this.automaton, t.automaton));
			}
		}))));
		this.setMember("<=", this.setMember("subset_language", this.setMember("subsetLanguage", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof HAObject)) throw new ScriptRuntimeError("HedgeAutomaton.subsetLanguageOf? expects HedgeAutomaton as argument");
				HAObject t = (HAObject)args.get(0);
				return ScriptObject.make(HAOps.subsetLanguage(HAObject.this.automaton, t.automaton));
			}
		})));
		this.setMember("<", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (! (args.get(0) instanceof HAObject)) throw new ScriptRuntimeError("< on HedgeAutomaton expects HedgeAutomaton as argument");
				HAObject t = (HAObject)args.get(0);
				return ScriptObject.make(HAOps.subsetLanguage(HAObject.this.automaton, t.automaton) && !HAOps.subsetLanguage(t.automaton, HAObject.this.automaton));
			}
		});
		
		this.setMember("to_fta", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				EasyFTA fta = FTAOps.ftaConverter(
						HAObject.this.automaton.getTA(),
						new Converter<HedgeState<State>,State>(){
							@Override
							public State convert(HedgeState<State> a) {
								return StateFactory.getStateFactory().makeState(a.toString());
							}
						},
						new Converter<HedgeSymbol<UnrankedSymbol>, RankedSymbol>(){
							@Override
							public RankedSymbol convert(HedgeSymbol<UnrankedSymbol> a) {
								return new StdNamedRankedSymbol<String>(a.toString(), a.getArity());
							}
						},
						new EasyFTACreator()
					);
				return new FTAObject(fta);
			}
		});
		
		this.setMember("states", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				List<ScriptObject> states = new ArrayList<ScriptObject>(HAObject.this.automaton.getStates().size());
				for (State state : HAObject.this.automaton.getStates()){
					states.add(ScriptObject.make(state.toString()));
				}
				return new ArrayObject(states);
			}
		});
		
		this.setMember("states", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				List<ScriptObject> finalstates = new ArrayList<ScriptObject>(HAObject.this.automaton.getStates().size());
				for (State state : HAObject.this.automaton.getFinalStates()){
					finalstates.add(ScriptObject.make(state.toString()));
				}
				return new ArrayObject(finalstates);
			}
		});
		
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof HAObject)) return false;
		return ((HAObject)o).getAutomaton().equals(this.automaton);
	}
	
	@Override
	public String toString(){
		return this.automaton.toString();
	}
	
	/**
	 * Returns the hedge automaton stored in this HAObject
	 * @return the hedge automaton stored in this HAObject
	 */
	public EasyHedgeAutomaton getAutomaton(){
		return this.automaton;
	}
	
	@Override
	public int hashCode(){
		return this.automaton.hashCode();
	}
}
