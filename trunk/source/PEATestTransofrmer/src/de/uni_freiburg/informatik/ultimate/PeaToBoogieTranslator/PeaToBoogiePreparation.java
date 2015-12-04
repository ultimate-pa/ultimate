package de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import pea.PhaseEventAutomata;

/**
 * Translates exaclty one Pea to Boogie AST snippets that have to be assembled from the outside.
 * This class translates without making any modifications to the pea, but derived classes are 
 * thought to make modifications, that can not be made in pea syntax e.g. appending a assert 
 * for testgeneration after the state guard has been evaluated.
 * 
 * @author langenfv@informatik.uni-freiburg.de
 *
 */
public class PeaToBoogiePreparation {
	
	private final static String PRIME_SYMBOL = "'";
	private final static String PHASE_COUNTER_PREFIX = "pc";
	
	protected Set<String> modifiedVariables = new HashSet<String>();
	protected List<String> clocks;
	protected HashMap<String, ArrayList<String>> varsByType = new HashMap<String, ArrayList<String>>();

	//Atomaton this class shall translate
	protected PhaseEventAutomata pea;
	protected int id;

	//TODO: deal with state, event, time, pc
	
	public PeaToBoogiePreparation(PhaseEventAutomata pea, int id){
		this.pea = pea;
		this.id = id;
		this.preProcessVariables();
	}
	
	/**
	 * Extract variables for final translation. Grouped by:
	 * - State variables
	 * - Events 
	 * - Clocks
	 * - PhaseCounter
	 * @param pea2
	 */
	private void preProcessVariables() {
		//phase counter
		String phaseCounter = PHASE_COUNTER_PREFIX + this.id;
		this.modifiedVariables.add(phaseCounter);
		this.varsByTypeAdd("int", phaseCounter);
		//clocks
		this.clocks.addAll(this.pea.getClocks());
		this.clocks = this.pea.getClocks();
		this.varsByTypeAdd("real", this.pea.getClocks());
		//state vars
		Map<String,String> vars = this.pea.getVariables();
		for(String ident: vars.keySet()){
			this.varsByTypeAdd(vars.get(ident), ident);
		}
	}
	
	/**
	 * Returns all variables necessary for the modifies statement.
	 * @return
	 */
	public Set<String> getModifiedVariables(){
		return this.modifiedVariables;		
	}
	
	private void varsByTypeAdd(String type, String ident){
		if(!this.varsByType.containsKey(type)){
			this.varsByType.put(type, new ArrayList<String>());
		}
		this.varsByType.get(type).add(ident);
	}
	private void varsByTypeAdd(String type, List<String> ident){
		if(!this.varsByType.containsKey(type)){
			this.varsByType.put(type, new ArrayList<String>());
		}
		this.varsByType.get(type).addAll(ident);
	}
	
}
