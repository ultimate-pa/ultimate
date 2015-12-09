package de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import pea.CDD;
import pea.PEATestAutomaton;
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
 * TODO: check if event vars are handled correctly
 *
 */
public class BasicTranslator {
	
	private final static String PRIME_SYMBOL = "'";
	protected final static String PHASE_COUNTER_PREFIX = "pc";
	
	private String fileName = "fileName";
	
	//All necessary information to translate the PEAs into a Boogie file is stored in the below structures
	private Set<String> modifiedVariables = new HashSet<String>();
	private Set<String> havocInLoop = new HashSet<String>();
	private Set<String> clocks = new HashSet<String>();
	private Set<String> vars = new HashSet<String>();
	private HashMap<String, HashSet<String>> varsByType = new HashMap<String, HashSet<String>>();
	protected HashMap<Integer, List<Phase>> initialEdgesAssume = new HashMap<Integer, List<Phase>>();
	private HashMap<Phase, ArrayList<Statement>> phaseInvariants = new HashMap<Phase, ArrayList<Statement>>();
	private HashMap<Transition, ArrayList<Statement>> transitionBody = new HashMap<Transition, ArrayList<Statement>>();

	//Atomaton this class shall translate
	private PhaseEventAutomata[] peas;
	private int id;
	private BoogieLocation noneLocation = new BoogieLocation(this.fileName,0,0,0,0,false);

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
		this.havocInLoop.add("delta");
		this.modifiedVariables.add("delta");
		//TODO: process variables here
		//collect the initial phases
		for(int i =0; i < peas.length; i++){
			this.preProcessInitialEdgesAssume(peas[i], i);
		}
		///from here on code is generated
		//make location invariants and transition bodies
		for(int i =0; i < peas.length; i++){
			BoogieLocation location = new BoogieLocation(this.fileName,i,i,0,0,false);
			this.generatePhaseInvariants(peas[i], this.fileName, location);
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
		statements.add(new AssertStatement(location, this.generateInitialPhaseAssumptionArgument(location, this.peas)));
		//add while body
		statements.add(new WhileStatement(
					location, 
					new WildcardExpression(location),
					new LoopInvariantSpecification[0],
					this.generateWhileBody(location)
					));
		return statements.toArray(new Statement[statements.size()]);
	}
	
	private Statement[] generateWhileBody(BoogieLocation location){
		ArrayList<Statement> statements = new ArrayList<Statement>();
		//havoc all primed, event, delta
		statements.add(this.generateWhileBodyHavoc(location));
		//assume delta > 0.0
		statements.add(new AssumeStatement(location,
				new BinaryExpression(location, BinaryExpression.Operator.COMPGT, 
						new IdentifierExpression(location, "delta"), new RealLiteral(location, Float.toString(0.0f)))));
		//every clock = clock + delta
		statements.addAll(this.generateClockUpdates(location, this.clocks));
		//generate phase invariants
		statements.addAll(this.generatePhases(location, this.peas));
		//genrate Edges
		statements.addAll(this.generateEdges(location,this.peas));
		//generate primes->vars
		for(String ident: this.vars){
			statements.add(new AssignmentStatement(location,
					new LeftHandSide[]{new VariableLHS(location,ident)},
					new Expression[]{new IdentifierExpression(location, ident+PRIME_SYMBOL)}));
		}
		return statements.toArray(new Statement[statements.size()]);
	}
	
	private ArrayList<Statement> generateEdges(BoogieLocation location, PhaseEventAutomata[] peas){
		ArrayList<Statement> statements = new ArrayList<Statement>();
		for(int i = 0; i < peas.length; i++){
			for(Statement statement: this.generateEdgesPerPea(location, i , peas[i])){
				statements.add(statement);
			}
		}
		return statements;
	}
	

	
	/**
	 * generate the edges of one pea
	 */
	private Statement[] generateEdgesPerPea(BoogieLocation location, int id, PhaseEventAutomata pea){
			Statement[] ifStatement = new Statement[]{
					this.generateIfPhaseCounterEquals(
									location, id, this.getNoOfPhase(pea, pea.getPhases()[0]), 
									this.generatePhaseEdges(location, id, pea, pea.getPhases()[0], this.transitionBody), 
									new Statement[]{})};
			for(int i = 1; i < pea.getPhases().length; i++){
				ifStatement = new Statement[]{
						this.generateIfPhaseCounterEquals(
										location, id, this.getNoOfPhase(pea, pea.getPhases()[i]),  
										this.generatePhaseEdges(location, id, pea, pea.getPhases()[i], this.transitionBody), 
										ifStatement)};
			}
			return ifStatement;	
	}	
	/**
	 * generate the edges of one phase
	 */
	private Statement[] generatePhaseEdges(BoogieLocation location, int id, PhaseEventAutomata pea, Phase phase,
			HashMap<Transition, ArrayList<Statement>> transitionBody){
		Statement[] ifStatement = new Statement[]{new AssumeStatement(location, new BooleanLiteral(location,false)) };
		for(int i = 0; i < phase.getTransitions().size(); i++){
			ifStatement = new Statement[]{this.generateIfWildcard(
					location,
					transitionBody.get(phase.getTransitions().get(i)), 
					ifStatement)};
		}
		return ifStatement;	
}

	
	private ArrayList<Statement> generatePhases(BoogieLocation location, PhaseEventAutomata[] peas){
		ArrayList<Statement> statements = new ArrayList<Statement>();
		for(int i = 0; i < peas.length; i++){
			for(Statement statement: this.generatePhase(location, i , peas[i], this.phaseInvariants)){
				statements.add(statement);
			}
		}
		return statements;
	}
	
	protected Statement[] generatePhase(BoogieLocation location, int id, PhaseEventAutomata pea, 
			HashMap<Phase, ArrayList<Statement>> phaseInvariants){
		Statement[] ifStatement = new Statement[]{
				this.generateIfPhaseCounterEquals(location, id, 0, phaseInvariants.get(pea.getPhases()[0]), new Statement[0])};
		for(int i = 1; i < pea.getPhases().length; i++){
			ifStatement = new Statement[]{this.generateIfPhaseCounterEquals(
					location, id, i, 
					phaseInvariants.get(pea.getPhases()[i]), 
					ifStatement)};
		}
		return ifStatement;
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
				this.transitionBody.get(transition).add(
							this.generateAssumeCDD(transition.getGuard(), file, location)
				);	
				//resets
				if (transition.getResets().length != 0) {
					for (int i = 0; i < transition.getResets().length; i++) {
						statements.add(this.generateClockReset(transition.getResets()[i], location));
					} 
			    }
				//successor
				int phaseIndex = this.getNoOfPhase(pea, transition.getDest());
		        statements.add(this.generateIntegerAssignment(PHASE_COUNTER_PREFIX+id, phaseIndex, location));
				
			}
		}
			
	}
	protected int getNoOfPhase(PhaseEventAutomata pea, Phase phase){
		//TODO: this is strange, 
        Phase[] phases = pea.getPhases();
        int phaseIndex = -1;
        for (int i = 0; i < phases.length; i++) {
        	if (phases[i].getName().equals(phase.getName())) phaseIndex = i;
        }
        return phaseIndex;
	}
	
	/**
	 * Generate the assume(clockInvariant);assume(phaseInvariant); per phase.
	 * Translation will simply use per phase the content of this.phaseInvariants .
	 * @param pea
	 * @param file
	 * @param location
	 */
	protected void generatePhaseInvariants(PhaseEventAutomata pea, String file, BoogieLocation location){
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
		String primedIdent;
		for(String ident: vars.keySet()){
			primedIdent = ident+PRIME_SYMBOL;
			this.varsByTypeAdd(vars.get(ident), ident);
			this.varsByTypeAdd(vars.get(ident), primedIdent);
			this.modifiedVariables.add(ident);
			this.modifiedVariables.add(primedIdent);
			this.havocInLoop.add(primedIdent);
			this.vars.add(ident);
		}
	}

	/**
	 * Add variables to the dictionary type->2^Vars
	 * @param type
	 * @param ident
	 */
	private void varsByTypeAdd(String type, String ident){
		if(!this.varsByType.containsKey(type)){
			this.varsByType.put(type, new HashSet<String>());
		}
		this.varsByType.get(type).add(ident);
	}
	private void varsByTypeAdd(String type, List<String> ident){
		if(!this.varsByType.containsKey(type)){
			this.varsByType.put(type, new HashSet<String>());
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
	protected VarList generateVarList(BoogieLocation location, String type, HashSet<String> idents){
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
	protected Statement generateInitialPhaseCounterHavoc(BoogieLocation location, PhaseEventAutomata[] peas){
		ArrayList<VariableLHS> vars = new ArrayList<VariableLHS>();
		for(int i = 0; i < peas.length; i++ ){
			vars.add(new VariableLHS(location, PHASE_COUNTER_PREFIX + i ));
		}
		return new HavocStatement(noneLocation, vars.toArray(new VariableLHS[vars.size()]));
	}
	protected Statement generateWhileBodyHavoc(BoogieLocation location){
		ArrayList<VariableLHS> vars = new ArrayList<VariableLHS>();
		for(String ident: this.havocInLoop){
			vars.add(new VariableLHS(location, ident ));
		}
		return new HavocStatement(noneLocation, vars.toArray(new VariableLHS[vars.size()]));
	}
	protected Expression generateInitialPhaseAssumptionArgument(BoogieLocation location, PhaseEventAutomata[] peas){
		ArrayList<Expression> conjunction = new ArrayList<Expression>();
		ArrayList<Expression> disjunctsPerPea;
		for(int key: this.initialEdgesAssume.keySet()){
			disjunctsPerPea = new ArrayList<Expression>();
			for(Phase phase: this.initialEdgesAssume.get(key)){
				disjunctsPerPea.add(new BinaryExpression(location, BinaryExpression.Operator.COMPEQ,
						new IdentifierExpression(location, PHASE_COUNTER_PREFIX+key), 
						new IntegerLiteral(location, Integer.toString(this.getNoOfPhase(peas[key], phase)))));
			}
			conjunction.add(this.generateBinaryLogicExpression(location, disjunctsPerPea, BinaryExpression.Operator.LOGICOR));
		}
		return this.generateBinaryLogicExpression(location, conjunction, BinaryExpression.Operator.LOGICAND);
	} 
	protected ArrayList<Statement> generateClockUpdates(BoogieLocation location, Set<String> clockIdents){
		ArrayList<Statement> updates = new ArrayList<Statement>();
		for(String ident: clockIdents){
			// clock := clock + delta;
			updates.add(new AssignmentStatement(location, 
					new VariableLHS[]{new VariableLHS(location, ident)}, 
					new Expression[]{new BinaryExpression(location,
							BinaryExpression.Operator.ARITHPLUS,
							new IdentifierExpression(location, "delta"),
							new IdentifierExpression(location, ident)
							)}));
		}
		return updates;
	}
	
	private Statement generateIfPhaseCounterEquals(BoogieLocation location, int id, int phase, 
			ArrayList<Statement> body, Statement[] elseIf){
		return this.generateIfPhaseCounterEquals(location, id, phase, body.toArray(new Statement[body.size()]), elseIf);
	}
		
	private Statement generateIfPhaseCounterEquals(BoogieLocation location, int id, int phase, 
			Statement[] body, Statement[] elseIf){
		return new IfStatement(location,
				new BinaryExpression(location,BinaryExpression.Operator.COMPEQ, 
						new IdentifierExpression(location, PHASE_COUNTER_PREFIX+id),
						new IntegerLiteral(location, Integer.toString(phase))),
				body,
				elseIf
		);
	}
	protected Statement generateIfWildcard(BoogieLocation location, ArrayList<Statement> body, Statement[] elseIf){
		return new IfStatement(location, new WildcardExpression(location),
				body.toArray(new Statement[body.size()]),
				elseIf
		);
	}
	
	protected Expression generateBinaryLogicExpression(BoogieLocation location, List<Expression> expressions, BinaryExpression.Operator operator){
		if(expressions.size() == 1){
			return expressions.get(0);
		}
		Expression term = new BinaryExpression(location, operator, 
				expressions.get(0), expressions.get(1));
		for(int i = 2; i < expressions.size(); i++){
			term = new BinaryExpression(location, operator, 
					term, expressions.get(i));
		}
		return term;
	}
	
}
