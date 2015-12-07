package de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;
import pea_to_boogie.translator.CDDTranslator;

/**
 * This is a basic PEA to Boogie translator.
 * This class handles the direct tanslation to boogie while the PeaToBoogiePreparation handles the
 * extraction of the required data from the peas themselves.
 * @author langenfv@informatik.uni-freiburg.de
 *
 */
public class BasicTranslator {
	
	private final static String PRIME_SYMBOL = "'";
	private final static String PHASE_COUNTER_PREFIX = "pc";
	
	private String fileName = "fileName";
	
	//All necessary information to translate the PEAs into a Boogie file is stored in the below structures
	protected Set<String> modifiedVariables = new HashSet<String>();
	protected Set<String> clocks = new HashSet<String>();
	protected HashMap<String, ArrayList<String>> varsByType = new HashMap<String, ArrayList<String>>();
	protected HashMap<Integer, List<Phase>> initialEdgesAssume = new HashMap<Integer, List<Phase>>();
	protected HashMap<Phase, ArrayList<Statement>> phaseInvariants = new HashMap<Phase, ArrayList<Statement>>();
	protected HashMap<Transition, ArrayList<Statement>> transitionBody = new HashMap<Transition, ArrayList<Statement>>();

	//Atomaton this class shall translate
	protected PhaseEventAutomata[] peas;
	protected int id;
	protected BoogieLocation noneLocation = new BoogieLocation(this.fileName,0,0,0,0,false);

	//TODO: deal with state, event, time, pc
	
	public BasicTranslator(PhaseEventAutomata[] peas){
		this.peas = peas;
		///preparation
		//collect all variables
		for(int i =0; i < peas.length; i++){
			this.preProcessVariables(peas[i], i);
		}
		//generate delta variable, that is shared by all automata
		this.varsByTypeAdd("real", "delta");
		//TODO: process variables here
		//collect the initial phases
		for(int i =0; i < peas.length; i++){
			this.preProcessInitialEdgesAssume(peas[i], i);
		}
		///from here on code is generated
		//make location invariants and transition bodies
		for(int i =0; i < peas.length; i++){
			BoogieLocation location = new BoogieLocation(this.fileName,i,i,0,0,false);
			this.generateStateInvariants(peas[i], this.fileName, location);
			this.generateTransitionBody(peas[i], i, this.fileName, location);
		}
		//generate boogie
	}
	
	public Unit generateBoogieTranslation(){
		BoogieLocation location = this.noneLocation;
		ArrayList<Declaration> declarations = new ArrayList<Declaration>();
		//inital variable declarations
		ArrayList<VarList> varLists = new ArrayList<VarList>();
		for(String type: this.varsByType.keySet()){
			varLists.add(this.generateVarList(location, type, this.varsByType.get(type)));
		}
		declarations.add(new VariableDeclaration(location, new Attribute[0], 
				varLists.toArray(new VarList[varLists.size()])));
		declarations.add(
				new Procedure(
				location,  
				new Attribute[0], 
				"executeModel", 
				new String[0],
				new VarList[0], 
				new VarList[0], 
				new Specification[]{this.generateModifiesVariable(location, this.modifiedVariables)}, 
				new Body(location, new VariableDeclaration[]{}, generateBodyStatements(location))
				) 
        );
		return new Unit(location, declarations.toArray(new Declaration[declarations.size()]));
	}
	
	private Statement[] generateBodyStatements(BoogieLocation location){
		ArrayList<Statement> statements = new ArrayList<Statement>();
		statements.add(this.generateInitialPhaseCounterHavoc(location, this.peas));
		//TODO: initial assumption
		statements.addAll(this.generatePhases(location));
		//TODO: generate Edges
		//TODO: generate primes->vars
		return statements.toArray(new Statement[statements.size()]);
	}
	
	private ArrayList<Statement> generatePhases(BoogieLocation location){
		ArrayList<Statement> statements = new ArrayList<Statement>();
		
		return statements;
	}
	
	/**
	 * Generates the body of the transitions.
	 */
	protected void generateTransitionBody(PhaseEventAutomata pea, int id, String file, BoogieLocation location){
		for(Phase phase: pea.getPhases()){
			for(Transition transition: phase.getTransitions()){
				ArrayList<Statement> statements = new ArrayList<Statement>();
				this.transitionBody.put(transition, statements);
				//guard
				//add invariant even if just assume(true) to prevent empty lists
				this.phaseInvariants.get(phase).add(
							this.generateAssumeCDD(transition.getGuard(), file, location)
				);	
				//resets
				if (transition.getResets().length != 0) {
					for (int i = 0; i < transition.getResets().length; i++) {
						statements.add(this.generateClockReset(transition.getResets()[i], location));
					} 
			    }
				//successor
				//TODO: this is strange, 
		        Phase desPhase = transition.getDest();
		        Phase[] phases = pea.getPhases();
		        int phaseIndex = -1;
		        for (int i = 0; i < phases.length; i++) {
		        	if (phases[i].getName().equals(desPhase.getName())) phaseIndex = i;
		        }
		        statements.add(this.generateIntegerAssignment(PHASE_COUNTER_PREFIX+id, phaseIndex, location));
				
			}
		}
			
	}
	
	/**
	 * Generate the assume(clockInvariant);assume(phaseInvariant); per phase.
	 * Translation will simply use per phase the content of this.phaseInvariants .
	 * @param pea
	 * @param file
	 * @param location
	 */
	protected void generateStateInvariants(PhaseEventAutomata pea, String file, BoogieLocation location){
		for(Phase phase: pea.getPhases()){
			this.phaseInvariants.put(phase, new ArrayList<Statement>());
			if(phase.getClockInvariant() != CDD.TRUE){
				this.phaseInvariants.get(phase).add(
						this.generateAssumeCDD(phase.getClockInvariant(), file, location)
						);	
			}
			//add invariant even if just assume(true) to prevent empty lists
			this.phaseInvariants.get(phase).add(
				this.generateAssumeCDD(phase.getStateInvariant(), file, location)
			);	
		}	
	}
	/**
	 * Collect all initial phases of all automata.
	 * @param pea
	 * @param id
	 */
	private void preProcessInitialEdgesAssume(PhaseEventAutomata pea, int id){
		this.initialEdgesAssume.put(id, new ArrayList<Phase>());
		for(Phase phase: pea.getInit()){
			this.initialEdgesAssume.get(id).add(phase);
		}
		
	}
	
	/**
	 * Extract variables for final translation. Grouped by:
	 * - State variables
	 * - Events 
	 * - Clocks
	 * - PhaseCounter
	 * @param pea2
	 */
	private void preProcessVariables(PhaseEventAutomata pea, int id) {
		//phase counter
		String phaseCounter = PHASE_COUNTER_PREFIX + id;
		this.modifiedVariables.add(phaseCounter);
		this.varsByTypeAdd("int", phaseCounter);
		//clocks
		this.clocks.addAll(pea.getClocks());
		this.varsByTypeAdd("real", pea.getClocks());
		this.modifiedVariables.addAll(pea.getClocks());
		//state vars
		Map<String,String> vars = pea.getVariables();
		for(String ident: vars.keySet()){
			this.varsByTypeAdd(vars.get(ident), ident);
			this.varsByTypeAdd(vars.get(ident), ident+PRIME_SYMBOL);
			this.modifiedVariables.add(ident);
			this.modifiedVariables.add(ident+PRIME_SYMBOL);
		}
	}

	/**
	 * Add variables to the dictionary type->2^Vars
	 * @param type
	 * @param ident
	 */
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
	
	/**
	 * Generate an assume( cdd ) statement from an CDD
	 */
	protected Statement generateAssumeCDD(CDD cdd, String file, BoogieLocation location){
		return new AssumeStatement(location,
				new CDDTranslator().CDD_To_Boogie(cdd,file,location));
	}
	/**
	 * Generate a clock reset statement for the transition.
	 */
	protected Statement generateClockReset(String ident, BoogieLocation location){
		VariableLHS identifier = new VariableLHS(location, ident);
    	RealLiteral dZero = new RealLiteral(location, Double.toString(0.0));
	    return new AssignmentStatement(location, new LeftHandSide[]{identifier}, new Expression[]{dZero});
	}
	/**
	 * Generate an integer assignment.
	 */
	protected Statement generateIntegerAssignment(String ident, int value, BoogieLocation location){
		VariableLHS identifier = new VariableLHS(location, ident);
    	IntegerLiteral dZero = new IntegerLiteral(location, Integer.toString(value));
	    return new AssignmentStatement(location, new LeftHandSide[]{identifier}, new Expression[]{dZero});
	}
	protected VarList generateVarList(BoogieLocation location, String type, List<String> idents){
		return new VarList(location, idents.toArray(new String[idents.size()]), 
				new PrimitiveType(location, type));
	}
	protected ModifiesSpecification generateModifiesVariable(BoogieLocation location, Set<String> idents){
		ArrayList<VariableLHS> vars = new ArrayList<VariableLHS>();
		for(String ident: idents){
			vars.add(new VariableLHS(location,ident));
		}
		return new ModifiesSpecification(location, false, vars.toArray(new VariableLHS[vars.size()]));
	}
	protected HavocStatement generateInitialPhaseCounterHavoc(BoogieLocation location, PhaseEventAutomata[] peas){
		ArrayList<VariableLHS> vars = new ArrayList<VariableLHS>();
		for(int i = 0; i < peas.length; i++ ){
			vars.add(new VariableLHS(location, PHASE_COUNTER_PREFIX + i ));
		}
		return new HavocStatement(noneLocation, vars.toArray(new VariableLHS[vars.size()]));
	}
	
}
