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
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.treetransducer;


import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTARule;
/**
 * Class to represent tree tranducers in an easy way.<br>
 * 
 * @see FTA
 * @see TTRuleSet
 * @see GenTT
 * 
 * @author Dorothea, Irene, Martin
 */
public class EasyTT extends GenTT<RankedSymbol,RankedSymbol,State>{


	/**
	 * Constructs a new tree transducer with given final states, 
	 * start alphabet, destination alphabet and rules.<br>
	 * The states are calculated from the rules.
	 * 
	 * @param finalStat final states
	 * @param startAlph start alphabet
	 * @param destAlph destination alphabet
	 * @param rul rules
	 * @param epsRul epsilon rules
	 */
	public EasyTT(Collection<State> finalStat, Collection<RankedSymbol> startAlph, Collection<RankedSymbol> destAlph, Collection<? extends TTRule<RankedSymbol,RankedSymbol,State>> rul, Collection<? extends TTEpsRule<RankedSymbol,State>> epsRul) {
		super(finalStat,startAlph,destAlph,new HashSet<TTRule<RankedSymbol,RankedSymbol,State>>(),new HashSet<TTEpsRule<RankedSymbol,State>>());
		Set<TTRule<RankedSymbol,RankedSymbol,State>> rul2 = new HashSet<TTRule<RankedSymbol,RankedSymbol,State>>();
		for (TTRule<RankedSymbol,RankedSymbol,State> r: rul){
			rul2.add(new TTRule<RankedSymbol,RankedSymbol,State>(r.getSymbol(),r.getSrcStates(),r.getDestState()));
		}
		Set<TTEpsRule<RankedSymbol,State>> epsRul2 = new HashSet<TTEpsRule<RankedSymbol,State>>();
		for (TTEpsRule<RankedSymbol,State> r: epsRul){
			epsRul2.add(new TTEpsRule<RankedSymbol,State>(r.getFirst(),r.getSecond()));
		}
		rules = new TTRuleSet<RankedSymbol,RankedSymbol,State>(rul2,epsRul2);
		
		finalStates.addAll(finalStates);
		preserveInvariants();
	}

	/**
	 * Constructs a new tree transducer with given final states, 
	 * start alphabet, destination alphabet and rules (without epsilon rules).<br>
	 * The states are calculated from the rules.
	 * 
	 * @param finalStat final states
	 * @param startAlph start alphabet
	 * @param destAlph destination alphabet
	 * @param rul rules
	 */
	public EasyTT(Collection<State> finalStat, Collection<RankedSymbol> startAlph, Collection<RankedSymbol> destAlph, Collection<? extends TTRule<RankedSymbol,RankedSymbol,State>> rul){
		super(finalStat,startAlph,destAlph,new HashSet<TTRule<RankedSymbol,RankedSymbol,State>>(),new HashSet<TTEpsRule<RankedSymbol,State>>());
		Set<TTRule<RankedSymbol,RankedSymbol,State>> rul2 = new HashSet<TTRule<RankedSymbol,RankedSymbol,State>>();
		for (TTRule<RankedSymbol,RankedSymbol,State> r: rul){
			rul2.add(new TTRule<RankedSymbol,RankedSymbol,State>(r.getSymbol(),r.getSrcStates(),r.getDestState()));
		}
		rules = new TTRuleSet<RankedSymbol,RankedSymbol,State>(rul2);
		preserveInvariants();
	}

	/**
	 * Constructs a new tree transducer with given final states and rules. <br>
	 * The states and alphabets are calculated from the rules.
	 * 
	 * @param finalStat final states
	 * @param rul rules
	 * @param epsRul epsilon rules
	 */
	public EasyTT(Collection<State> finalStat, Collection<? extends TTRule<RankedSymbol,RankedSymbol,State>> rul, 
			Collection<? extends TTEpsRule<RankedSymbol,State>> epsRul) {
		super(finalStat,new HashSet<TTRule<RankedSymbol,RankedSymbol,State>>(),new HashSet<TTEpsRule<RankedSymbol,State>>());
		Set<TTRule<RankedSymbol,RankedSymbol,State>> rul2 = new HashSet<TTRule<RankedSymbol,RankedSymbol,State>>();
		for (TTRule<RankedSymbol,RankedSymbol,State> r: rul){
			rul2.add(new TTRule<RankedSymbol,RankedSymbol,State>(r.getSymbol(),r.getSrcStates(),r.getDestState()));
		}
		Set<TTEpsRule<RankedSymbol,State>> epsRul2 = new HashSet<TTEpsRule<RankedSymbol,State>>();
		for (TTEpsRule<RankedSymbol,State> r: epsRul){
			epsRul2.add(new TTEpsRule<RankedSymbol,State>(r.getSrcState(),r.getDestState()));
		}
		
		rules = new TTRuleSet<RankedSymbol,RankedSymbol,State>(rul2,epsRul2);

		finalStates.addAll(finalStates);
		preserveInvariants();
	}
	/**
	 * Constructs a new tree transducer with given final states and rules. <br>
	 * The states and alphabets are calculated from the rules.
	 * 
	 * @param finalStat final states
	 * @param rul rules
	 */
	public EasyTT(Collection<State> finalStat, Collection<? extends TTRule<RankedSymbol,RankedSymbol,State>> rul) {
		super(finalStat,new HashSet<TTRule<RankedSymbol,RankedSymbol,State>>(),new HashSet<TTEpsRule<RankedSymbol,State>>());
		Set<TTRule<RankedSymbol,RankedSymbol,State>> rul2 = new HashSet<TTRule<RankedSymbol,RankedSymbol,State>>();
		for (TTRule<RankedSymbol,RankedSymbol,State> r: rul){
			rul2.add(new TTRule<RankedSymbol,RankedSymbol,State>(r.getSymbol(),r.getSrcStates(),r.getDestState()));
		}
		rules = new TTRuleSet<RankedSymbol,RankedSymbol,State>(rul2);

		finalStates.addAll(finalStates);
		preserveInvariants();
	}
	

	/**
	 * A part of the functionality of a tree transducer is the same as the one of a finite tree automaton.
	 * Thus such a corresponding the finite tree automaton can be obtained from the transducer by 
	 * transforming the rules (just the first parameter of each right side is needed).
	 * 
	 * @return the finite tree automaton which is inside the tree transducer
	 */
	@Override
	public EasyFTA getFTAPart(){
		List<EasyFTARule> newrules = new LinkedList<EasyFTARule>();
		for (TTRule<RankedSymbol, RankedSymbol, State> rule: rules.getRulesAsList()){
			newrules.add(new EasyFTARule(rule.getSymbol(),rule.getSrcStatesAsQ(),rule.getDestStateAsQ()));
		}
		List<State> finals = new LinkedList<State>();
		for (TTState<State, RankedSymbol> qf: finalStates){
			finals.add(qf.getState());
		}
		EasyFTA epsfta = new EasyFTA(newrules, finals);
		epsfta.addSymbols(this.startAlphabet);
		return epsfta;
	}

}
