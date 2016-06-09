

























package pea_to_boogie.translator;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import pea.Phase;
import pea.PhaseBits;
import pea.PhaseEventAutomata;
import pea.Transition;
import pea_to_boogie.generator.ConditionGenerator;
import pea_to_boogie.generator.Permutation;
import req_to_pea.ReqToPEA;
import srParse.pattern.PatternType;
/**
 * This class translates a phase event automaton to an equivalent Boogie code.
 */
public class Translator {
	
	/**
	 * The name of the input file containing the requirements/peas.
	 */
	public String inputFilePath;

    /**
     * The address of the Boogie text file.
     */
    public String boogieFilePath;
    /**
     * The unit that contains declarations.
     */
    public Unit unit;
    /**
     * The list of declarations.
     */
    public List<Declaration> decList = new ArrayList<Declaration>();
    /**
     * The list of clock identifiers.
     */
    public List<String> clockIds = new ArrayList<String>();
    /**
     * The list of unique identifiers. Each identifier is in the form of "pc" + phaseIndex.
     * Each automaton has an array of phases. The location of each phase in that array specifies the
     * value of phaseIndex.    
     */
    public List<String> pcIds = new ArrayList<String>();
    /**
     * The list of state variables and according types.
     */
    public Map<String,String> stateVars = new HashMap<String,String>();
    /**
     * The list of primed variables.
     */
    public List<String> primedVars = new ArrayList<String>();
    /**
     * The list of events.
     */
    public List<String> eventVars = new ArrayList<String>();
    /**
     * The list of automata.
     */
    public PhaseEventAutomata[] automata;
    /**
     * The array of input requirements.
     */
    public PatternType[] mRequirements;
    
    
    /**
     * The properties for which we check for vacuity. 
     */
    public BitSet mVacuityChecks;
    /**
     * The value of combinations of automata. 
     */
    public int combinationNum;
    
    /**
     * The boogie locations used to annotate the boogie code.
     * This array contains the location for requirement reqNr in
     * index reqNr+1 and the location for code that is not 
     * specific to any requirements in index 0.
     */
    public BoogieLocation[] boogieLocations;
    
    /**
     * Set the input file name.  This is used to annotate the
     * Boogie code with the right file name.  The Location object
     * should contain the name of the original file name.  
     * @param The input file name.
     */
    public void setInputFilePath(String path) {
		inputFilePath = path;
    }
    public String getInputFilePath() {
    	return inputFilePath;
    }
    
    /**
     * Assign an address to the boogieFilePath.  
     * @param The address of a Boogie text file.
     */
    public void setBoogieFilePath(String path) {
		boogieFilePath = path;
    }
    /**
     * 
     * @return The address of a Boogie text file.
     */
    public String getBoogieFilePath() {
		return boogieFilePath;
    }
    
    /**
     * Add a bitset containing the numbers of the components for which vacuity
     * should be checked.
     * @param vacuityChecks the bitset. Bit i is set if we should check vacuity 
     * for the i-th property.
     */
    public void setVacuityChecks(BitSet vacuityChecks) {
		mVacuityChecks = vacuityChecks;
    }
    
    public boolean checkVacuity(int propertyNum) {
    	return mVacuityChecks != null && mVacuityChecks.get(propertyNum);
    }
    
    /**
     * Assign a value to the combinationNum.
     * @param num
     */
    public void setCombinationNum(int num) {
		combinationNum = num;
    }
    
    /**
     * Generate global variables. 
     */
    public void genGlobVars() {
    	
       try {
			final BoogieLocation blUnit = boogieLocations[0];
			final BoogieLocation blVar = blUnit;
			final BoogieLocation blPrimType = blUnit;
         
			for (int i = 0; i < automata.length; i++) {
				final List<String> tempClocks = automata[i].getClocks();
        	  for (int j = 0; j < tempClocks.size(); j++) {  
					clockIds.add(tempClocks.get(j));
              }            
          }
          ASTType astType = new PrimitiveType(blPrimType, "real"); 
			final VarList clockVars = new VarList(blVar, clockIds.toArray(new String[clockIds.size()]), astType);
          
			final List<String> extraVars = new ArrayList<String>();
			for (int i = 0; i < automata.length; i++) {
				pcIds.add("pc" + i);
        	  extraVars.add("pc"+i);
          }
          astType = new PrimitiveType(blPrimType, "int");
			final VarList pcVar = new VarList(blVar, extraVars.toArray(new String[extraVars.size()]), astType);
          
          //collect global vars from system states
          boolean visited = false;
			for (int i = 0; i < automata.length; i++) {
        	  // System.out.println(this.automata[i].getVariables().size());

				final Map<String, String> map = automata[i].getVariables();
    	    
				for (final String name : map.keySet()) {
      			  //every var that is not an event var must be a state var, as clocks
      			  //are stored seperately
      			  if (!map.get(name).equals("event")){
						for (int j = 0; j < stateVars.size(); j++) {
							if (name.equals(stateVars.get(j))) {
    	    				  visited = true;
    	    				  break; 
    	    			  }
    	    		  }
    	    		  if (!visited) {
    	    			  this.stateVars.put(name, map.get(name));
    	    			  this.primedVars.add(name + "'");
    	    		  }

    	    	  } else {
						for (int j = 0; j < eventVars.size(); j++) {
							if (name.equals(eventVars.get(j))) {
    	    				  visited = true;
    	    				  break;
    	    			  }
    	    		  }
    	    		  if (!visited) {
							eventVars.add(name);
    	    		  }
    	    	  }
    	    	  visited = false; 
    	      } 
          }                          
          extraVars.clear();
          extraVars.add("delta");
          astType = new PrimitiveType(blPrimType, "real");
			final VarList deltaVar = new VarList(blVar, extraVars.toArray(new String[extraVars.size()]), astType);
			final List<VarList> varList = new ArrayList<VarList>();
			if (!clockIds.isEmpty()) {
        	  varList.add(clockVars);
			}
          varList.add(pcVar);
          varList.add(deltaVar);
          
			if (stateVars.size() != 0) {
        	  for(String name : this.stateVars.keySet()){
	              astType = new PrimitiveType(blPrimType, this.stateVars.get(name)); 
	              List<String> stVarsList = new ArrayList<String>();




	              
	            	  stVarsList.add(name);
	            	  stVarsList.add(name + "'");
	              
	              VarList stVars = new VarList(blVar, stVarsList.toArray(new String[stVarsList.size()]),

	              		  astType); 
	        	  varList.add(stVars);
        	  }
          }
          
			if (eventVars.size() != 0) {
              astType = new PrimitiveType(blPrimType, "bool"); 
				final VarList evVars = new VarList(blVar, eventVars.toArray(new String[eventVars.size()]), astType);
        	  varList.add(evVars);
          }
			final Attribute[] attribute = new Attribute[0];
			final VariableDeclaration vars = new VariableDeclaration(blVar, attribute,
        		  varList.toArray(new VarList[varList.size()]));
			decList.add(vars);
			final Declaration[] decArray = decList.toArray(new Declaration[decList.size()]);
			unit = new Unit(blUnit, decArray);
		} catch (final Exception e) {
    	   e.printStackTrace();
       }
    }
    /**
     * Generate the conjunction of a list of expressions.
     * @param exprs list of expressions.
     * @param bl Boogie location. 
     * @return the CNF of a list of expressions.
     */
    public Expression genConjunction (List<Expression> exprs, BoogieLocation bl) {
		final Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext()) {
    		return new BooleanLiteral(bl, true);
		}
    	Expression cnf = it.next();
    	while (it.hasNext()) {
    		cnf = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND,
    				cnf, it.next());
  	    }
    	return cnf;
    }
    /**
     * Generate the disjunction of a list of expressions.
     * @param exprs list of expressions.
     * @param bl Boogie location. 
     * @return the CNF of a list of expressions.
     */
    public Expression genDisjunction (List<Expression> exprs, BoogieLocation bl) {
		final Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext()) {
    		return new BooleanLiteral(bl, false);
		}
    	Expression cnf = it.next();
    	while (it.hasNext()) {
    		cnf = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR,
    				cnf, it.next());
  	    }
    	return cnf;
    }
    /**
     * Generate time passing.
     * @param clock identifier.
     * @param Boogie location.
     * @return time passing statement. 
     */
    public Statement genClockPlusDelta(String clockId, BoogieLocation bl) {
		final VariableLHS clockVar = new VariableLHS(bl, clockId);
	    
		final IdentifierExpression clockID = new IdentifierExpression(bl, clockId);
		final IdentifierExpression deltaID = new IdentifierExpression(bl, "delta");
		final BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.ARITHPLUS, clockID, deltaID);
		final LeftHandSide[] lhs = new LeftHandSide[1];
	    lhs[0] = clockVar;
		final Expression[] expr = new Expression[1];
	    expr[0] = binaryExpr;
		final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
	    
    	return assignment;
    }
    
    /**
     * Generate the delay statements and havoc all primed variables and event variables. 
     * The code has the form
     * <pre>
     * 	   havoc primedVars, eventVars, delta;
     *     assume delta > 0.0
     *     clock1 := clock + delta;
     *     ...
     * </pre>
     * @param bl
     * @return
     */
    public Statement[] genDelay(BoogieLocation bl) {
    	
		final List<VariableLHS> havocIds = new ArrayList<VariableLHS>();
		for (int i = 0; i < primedVars.size(); i++) {
			havocIds.add(new VariableLHS(bl, primedVars.get(i)));
    	}
		for (int i = 0; i < eventVars.size(); i++) {
			havocIds.add(new VariableLHS(bl, eventVars.get(i)));
    	}
    	havocIds.add(new VariableLHS(bl, "delta"));   	
		final VariableLHS[] ids = havocIds.toArray(new VariableLHS[havocIds.size()]);
		final HavocStatement havocSmt = new HavocStatement(bl, ids);
		final IdentifierExpression identifier = new IdentifierExpression(bl, "delta");
		final RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0.0));
		final BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPGT, identifier,
				realLiteral);
		final AssumeStatement assumeDelta = new AssumeStatement(bl, binaryExpr);
    	
		final Statement[] smtArray = new Statement[clockIds.size()];
		for (int i = 0; i < clockIds.size(); i++) {
			smtArray[i] = genClockPlusDelta(clockIds.get(i), bl);
    	}    	  	
		final Statement[] statements = new Statement[smtArray.length + 2];
    	statements[0] = havocSmt;
    	statements[1] = assumeDelta;
    	for (int i = 2; i < statements.length; i++) {

    		statements[i] = smtArray[i-2];
    	}
    	return statements;
    }
    /**
     * Generate the expression <code>pc<i>autIndex</i> == <i>phaseIndex</i></code> that checks
     * if the automaton autIndex is currently in the phase phaseIndex.
     * @param phaseIndex the index of the phase we check for.
     * @param autIndex   the index of the automaton.
     * @param bl
     * @return
     */
    public Expression genComparePhaseCounter (int phaseIndex, int autIndex, BoogieLocation bl) {
		final IdentifierExpression identifier = new IdentifierExpression(bl, "pc" + autIndex);
		final IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(phaseIndex));
		final BinaryExpression ifCon = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier, intLiteral);
    	return ifCon;
    }
    /**
     * Creates the code that checks the phase invariant of the given phase.
     * @param phase the phase whose invariant should be checked.
     * @param bl
     * @return the array of (two) statements that check the invariant.
     */
    public Statement[] genCheckPhaseInvariant(Phase phase, BoogieLocation bl) {
 	    Expression expr	= new CDDTranslator().CDD_To_Boogie(phase.getClockInvariant(),getBoogieFilePath(), bl);
		final AssumeStatement assumeClInv = new AssumeStatement(bl, expr);
     	expr = new CDDTranslator().CDD_To_Boogie(phase.getStateInvariant(),getBoogieFilePath(), bl);
		final AssumeStatement assumeStateInv = new AssumeStatement(bl, expr);
		final Statement[] statements = new Statement[2];
    	statements[0] = assumeClInv;
    	statements[1] = assumeStateInv;
    	return statements;
    }
    public Statement joinIfSmts (Statement[] statements, BoogieLocation bl) {
    	
		final List<Statement> smtList = new ArrayList<Statement>();
    	for (int i = 0; i < statements.length; i++) {
			final IfStatement oldIfSmt = (IfStatement) statements[i];
    		if (smtList.size() == 0) {
				final Statement[] emptyArray = new Statement[0];
				final IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), emptyArray);
           	smtList.add(newIfSmt);
    		} else {
				final Statement[] smt = new Statement[1];
    			smt[0] = smtList.get(smtList.size()-1);
				final IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
              	smtList.add(newIfSmt);
    		}
    	}
    	  
    	return smtList.get(smtList.size()-1);
    }
    public Statement joinInnerIfSmts (Statement[] statements, BoogieLocation bl) {
    	
		final List<Statement> smtList = new ArrayList<Statement>();
    	for (int i = 0; i < statements.length; i++) {
			final IfStatement oldIfSmt = (IfStatement) statements[i];
    		if (smtList.size() == 0) {
				final BooleanLiteral bLiteral = new BooleanLiteral(bl, false);
				final AssumeStatement assumeFalse = new AssumeStatement(bl, bLiteral);
				final Statement[] smt = new Statement[1];
    	     smt[0] = assumeFalse;
				final IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
           	smtList.add(newIfSmt);
    		} else {
				final Statement[] smt = new Statement[1];
    			smt[0] = smtList.get(smtList.size()-1);
				final IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
              	smtList.add(newIfSmt);
    		}
    	}
    	  
    	return smtList.get(smtList.size()-1);
    }
    
    /**
     * Check the invariants of the given automaton.  This is an if statement that first checks
     * in which phase the automaton is and then checks the corresponding invariants.
     * @param automaton  the automaton to check.
     * @param autIndex   the index of the automaton to check.
     * @param bl  The location information to correspond the generated source to
     * 	the property.
     * @return The if statement checking the p
     */
    public Statement genCheckInvariants(PhaseEventAutomata automaton, int autIndex, BoogieLocation bl) {
    	
		final Phase[] phases = automaton.getPhases();
		final Statement[] statements = new Statement[phases.length];
    	for (int i = 0; i < phases.length; i++) {
			final Expression ifCon = genComparePhaseCounter(i, autIndex, bl);
			final Statement[] emptyArray = new Statement[0];
			final IfStatement ifStatement = new IfStatement(bl, ifCon, genCheckPhaseInvariant(phases[i], bl), emptyArray);
    		statements[i] = ifStatement;
    	}
		final Statement statement = joinIfSmts(statements, bl);
    	return statement;
    }
    public Statement genReset(String resetVar, BoogieLocation bl) {
		final VariableLHS reset = new VariableLHS(bl, resetVar);
     	
		final RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0.0));
		final LeftHandSide[] lhs = new LeftHandSide[1];
	    lhs[0] = reset;
		final Expression[] expr = new Expression[1];
	    expr[0] = realLiteral;
		final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
	    
    	return assignment;
    }
    public Statement genPCAssign(int autIndex, int phaseIndex, BoogieLocation bl) {
		final VariableLHS pc = new VariableLHS(bl, "pc" + autIndex);
     	
		final IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(phaseIndex));
		final LeftHandSide[] lhs = new LeftHandSide[1];
	    lhs[0] = pc;
		final Expression[] expr = new Expression[1];
	    expr[0] = intLiteral;
		final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
	    
    	return assignment;
    }

    public Statement[] genInnerIfBody(PhaseEventAutomata automaton, Transition transition, 
    		int autIndex, BoogieLocation bl) {
           	
		final List<Statement> smtList = new ArrayList<Statement>();
    //	StringLiteral strLiteral = new StringLiteral(blAssumeGuard, 
  	//    		CDDTranslation.CDD_To_Boogie(transition.getGuard()));
		final Expression expr = new CDDTranslator().CDD_To_Boogie(transition.getGuard(), getBoogieFilePath(), bl);
		final AssumeStatement assumeGuard = new AssumeStatement(bl, expr);
      	smtList.add(assumeGuard);
        if (transition.getResets().length != 0) {
			final String[] resets = transition.getResets();
        	for (int i = 0; i < resets.length; i++) {
        		smtList.add(genReset(resets[i], bl));
        	} 
        }
		final Phase desPhase = transition.getDest();
		final Phase[] phases = automaton.getPhases();
        int phaseIndex = -1;
        for (int i = 0; i < phases.length; i++) {
			if (phases[i].getName().equals(desPhase.getName())) {
				phaseIndex = i;
			}
		}
        smtList.add(genPCAssign(autIndex, phaseIndex, bl));
        
		final Statement[] statements = smtList.toArray(new Statement[smtList.size()]);
    	return statements;
    }
    
    public Statement genOuterIfBody(PhaseEventAutomata automaton, Phase phase, int autIndex, BoogieLocation bl) {
    	
		final Statement[] statements = new Statement[phase.getTransitions().size()];
		final List<Transition> transitions = phase.getTransitions();
    	for (int i = 0; i < transitions.size(); i++) {
			final WildcardExpression wce = new WildcardExpression(bl);
			final Statement[] emptyArray = new Statement[0];
			final IfStatement ifStatement = new IfStatement(bl, wce,
       			 genInnerIfBody(automaton, transitions.get(i), autIndex, bl), emptyArray);
       	 statements[i] = ifStatement;
      	}
		final Statement statement = joinInnerIfSmts(statements, bl);
    	
    	return statement;
    } 
    public Statement genOuterIfTransition(PhaseEventAutomata automaton, int autIndex, BoogieLocation bl) {
	   	
		final Phase[] phases = automaton.getPhases();
		final Statement[] statements = new Statement[phases.length];
    	for (int i = 0; i < phases.length; i++) {
			final Expression ifCon = genComparePhaseCounter(i, autIndex, bl);
			final Statement[] emptyArray = new Statement[0];
			final Statement[] outerIfBodySmt = new Statement[1];
     	  outerIfBodySmt[0] = genOuterIfBody(automaton, phases[i], autIndex, bl);
			final IfStatement ifStatement = new IfStatement(bl, ifCon, outerIfBodySmt, emptyArray);
     	 statements[i] = ifStatement;
    	}
		final Statement statement = joinIfSmts(statements, bl);
    	
    	return statement;
    }
    public List<Statement> genStateVarsAssign(BoogieLocation bl){
      List<Statement> statements = new ArrayList<Statement>();
      for(String name: this.stateVars.keySet()) { 
 	    VariableLHS lhsVar = new VariableLHS(bl, name);
    	IdentifierExpression rhs = new IdentifierExpression(bl, name+"'");
 	    LeftHandSide[] lhs = new LeftHandSide[1];
 	    lhs[0] = lhsVar;
			final Expression[] expr = new Expression[1];
	    expr[0] = rhs;
			final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
 	    statements.add(assignment);
      }
    	return statements;
    }
    public Statement genAssertRTInconsistency(int[] permutation, BoogieLocation bl) {
		final ConditionGenerator conGen = new ConditionGenerator();
     	conGen.setTranslator(this);
		final Expression expr = conGen.nonDLCGenerator(automata, permutation, getBoogieFilePath(), bl);
		if (expr == null) {
			return null;
		}
		final ReqCheck check = new ReqCheck(ReqCheck.ReqSpec.RTINCONSISTENT, permutation, this);
		final ReqLocation loc = new ReqLocation(check);
		final AssertStatement assertSmt = new AssertStatement(loc, expr);
    	return assertSmt;
    }
    /**
     * Generate the assertion that is violated if the requirement represented by the given 
     * automaton is non-vacuous.  The assertion expresses that the automaton always stays in the
     * early phases and never reaches the last phase.  It may be false if all phases of the
     * automaton are part of the last phase, in which case this function returns null.
     * @param pea The automaton for which vacuity is checked.
     * @param automatonIndex The number of the automaton.
     * @param bl A boogie location used for all statements.
     * @return The assertion for non-vacousness or null if the assertion would be false.
     */
    private Statement genAssertNonVacuous(PhaseEventAutomata pea,
			int automatonIndex, BoogieLocation bl) {
		final Phase[] phases = pea.getPhases();

    	// compute the maximal phase number occurring in the automaton. 
    	int maxBits = 0;
		for (final Phase phase : phases) {
			final PhaseBits bits = phase.getPhaseBits();
			// ignore start node when computing max phase 
    		if (bits != null) {
				final int act = bits.getActive();
	    		if (act > maxBits) {
	    			maxBits = act;
	    		}
    		}
    	}
    	int pnr = 0;
		while ((1 << pnr) <= maxBits) {
    		pnr++;
		}
    	
    	// check that one of those phases is eventually reached.
		final List<Expression> checkReached = new ArrayList<Expression>();
    	for (int i = 0; i < phases.length; i++) {
			final PhaseBits bits = phases[i].getPhaseBits();
			if (bits == null || (bits.getActive() & (1 << (pnr - 1))) == 0) {
    			checkReached.add(genComparePhaseCounter(i, automatonIndex, bl));
			}
		}
		if (checkReached.isEmpty()) {
    		return null;
		}
		final Expression disjunction = genDisjunction(checkReached, bl);
		final ReqCheck check = new ReqCheck(ReqCheck.ReqSpec.VACUOUS, new int[] { automatonIndex }, this);
		final ReqLocation loc = new ReqLocation(check);
		return new AssertStatement(loc, disjunction);
	}
    /**
     * Create the statements of the main loop of the pea product.  The main loop looks like this
     * <pre>
     *    delay statements (havoc delay, eventVar, primedVars, add delay to all clocks)
     *    check invariants of phases
     *    assert reachability
     *    check transitions
     * </pre>
     *  
     * @param bl
     *          Location of the procedure body.
     * @return
     *        Statements of the while-body.
     */
    public Statement[] genWhileBody (BoogieLocation bl) {
    	List<Statement> stmtList = new ArrayList<Statement>();
    	stmtList.addAll(Arrays.asList(genDelay(bl)));
       
		for (int i = 0; i < automata.length; i++) {
			stmtList.add(genCheckInvariants(automata[i], i, bl));
    	}
		final int[] automataIndices = new int[automata.length];
		for (int i = 0; i < automata.length; i++) {
    		automataIndices[i] = i;
    	}
		for (final int[] subset : new Permutation().subArrays(automataIndices, combinationNum)) {
			final Statement assertStmt = genAssertRTInconsistency(subset, bl);
			if (assertStmt != null) {
    			stmtList.add(assertStmt);
			}
		}
		for (int i = 0; i < automata.length; i++) {
    		if (checkVacuity(i)) {
				final Statement assertStmt = genAssertNonVacuous(automata[i], i, bl);
				if (assertStmt != null) {
        			stmtList.add(assertStmt);
				}
			}
		}


		for (int i = 0; i < automata.length; i++) {
			stmtList.add(genOuterIfTransition(automata[i], i, bl));
    	}
		if (stateVars.size() != 0) {
			final List<Statement> stateVarsAssigns = genStateVarsAssign(bl);
   	    	for (int i = 0; i < stateVarsAssigns.size(); i++) {
   	    		stmtList.add(stateVarsAssigns.get(i));
   	    	} 
   	    }
    	
    	Statement[] statements = stmtList.toArray(new Statement[stmtList.size()]);
    	return statements;
    }
    
	/**
     * Create the main loop of the pea product.  This is a huge while statement that
     * contains all transitions of all components.  This procedure calls
     * {@link genWhileBody} to create the statements of the main loop.
     *  
     * @param bl
     *          Location of the procedure body.
     * @return
     *        The while-statement.
     */
    public Statement genWhileSmt (BoogieLocation bl) {
		final WildcardExpression wce = new WildcardExpression(bl);
		final LoopInvariantSpecification[] invariants = new LoopInvariantSpecification[0];
		final WhileStatement whileStatement = new WhileStatement(bl, wce, invariants, genWhileBody(bl));
    	return whileStatement;
    }
    public Expression genPcExpr(Phase[] phases,Phase[] initialPhases, int autIndex, BoogieLocation bl) {
		final List<Expression> exprList = new ArrayList<Expression>();
    	for (int i = 0; i < phases.length; i++) {
    		for (int j = 0; j < initialPhases.length; j++) {
    			if (phases[i].getName().equals(initialPhases[j].getName())) {
    				phases[i].setInit(true);
    				break;
    			}
    		}
    	}
    	for (int i = 0; i < phases.length; i++) {
	      if (phases[i].isInit) {	
				final IdentifierExpression identifier = new IdentifierExpression(bl, "pc" + autIndex);
				final IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(i));
 	     	BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ,
 	     			identifier, intLiteral);
    		if (exprList.size() == 0) {
              exprList.add(binaryExpr);
    		} else {
     	        binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR,
     	     			exprList.get(exprList.size()-1), binaryExpr);
     	        exprList.add(binaryExpr);
    		}
	      }
    	}
    	return exprList.get(exprList.size()-1);
    } 
    public Statement[] genInitialPhasesSmts (BoogieLocation bl) {
		final VariableLHS[] ids = new VariableLHS[pcIds.size()];
		for (int i = 0; i < pcIds.size(); i++) {
			ids[i] = new VariableLHS(bl, pcIds.get(i));
    	}
		final HavocStatement pcHavoc = new HavocStatement(bl, ids);
    	
		final List<Expression> pcExprs = new ArrayList<Expression>();
		for (int i = 0; i < automata.length; i++) {
			pcExprs.add(genPcExpr(automata[i].getPhases(), automata[i].getInit(), i, bl));
    	}
    	
		final AssumeStatement assumeSmt = new AssumeStatement(bl, genConjunction(pcExprs, bl));
    	
		final Statement[] statements = new Statement[2];
    	statements[0] = pcHavoc;
    	statements[1] = assumeSmt;
    	return statements;
    }
    public Expression genClockInit (BoogieLocation bl) {
    	Expression initializer = null;
		for (int i = 0; i < clockIds.size(); i++) {
			final IdentifierExpression identifier = new IdentifierExpression(bl, clockIds.get(i));
			final RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0));
			final BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier,
					realLiteral);
    		if (initializer == null) {
    			initializer = binaryExpr;
    		} else {
     	        initializer = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND,
     	     			initializer, binaryExpr);
    		}
    	}
		if (initializer == null) {
    		initializer = new BooleanLiteral(bl, true);
		}
    	return initializer;
    }
    public Statement[] genClockInitSmts (BoogieLocation bl) {
    	if (clockIds.isEmpty()) {
    		return new Statement[0];
    	}
		final VariableLHS[] clocks = new VariableLHS[clockIds.size()];
    	int i=0;
		for (final String clkId : clockIds) {
    		clocks[i++] = new VariableLHS(bl, clkId);
		}
		final HavocStatement clockHavoc = new HavocStatement(bl, clocks);
		final AssumeStatement assumeSmt = new AssumeStatement(bl, genClockInit(bl));
     	
		final Statement[] statements = new Statement[2];
     	statements[0] = clockHavoc;
     	statements[1] = assumeSmt;

    	return statements;
    }
    
    /**
     * One assignment is initialized (only as an example).
     * The genWhileSmt method is called.     
     * @param bl
     *          Location of the procedure body.
     * @return
     *        Statements of the procedure body which includes one assignment and one while-statement.
     */
    public Statement[] genProcBodySmts (BoogieLocation bl) {
		final List<Statement> statements = new ArrayList<Statement>();
    	statements.addAll(Arrays.asList(genInitialPhasesSmts (bl)));
    	statements.addAll(Arrays.asList(genClockInitSmts (bl)));
    	statements.add(genWhileSmt(bl));
    	return statements.toArray(new Statement[statements.size()]);
    }
    /**
     * The procedure statement is initialized. It is deployed to the unit.
     * The unit is sent to the print process. The result is a Boogie text file. 
     */
    public Unit genProc () {
		final BoogieLocation bl = boogieLocations[0];
		final VariableDeclaration[] localVars = new VariableDeclaration[0];
		final Body body = new Body(bl, localVars, genProcBodySmts(bl));
		final List<String> modifiedVarsList = new ArrayList<String>();
		for (int i = 0; i < clockIds.size(); i++) {
			modifiedVarsList.add(clockIds.get(i));
        }
		for (int i = 0; i < pcIds.size(); i++) {
			modifiedVarsList.add(pcIds.get(i));
        }
        modifiedVarsList.add("delta");
        
        for (String name: this.stateVars.keySet()) {
        	modifiedVarsList.add(name);
        	modifiedVarsList.add(name+"'");
        }
        
		for (int i = 0; i < eventVars.size(); i++) {
			modifiedVarsList.add(eventVars.get(i));
        }
		final VariableLHS[] modifiedVars = new VariableLHS[modifiedVarsList.size()];
        for (int i = 0; i < modifiedVars.length; i++) {
        	modifiedVars[i] = new VariableLHS(bl, modifiedVarsList.get(i));
        }       
		final ModifiesSpecification mod = new ModifiesSpecification(bl, false, modifiedVars);
		final ModifiesSpecification[] modArray = new ModifiesSpecification[1];
        modArray[0] = mod;
		final Attribute[] attribute = new Attribute[0];
		final String[] typeParams = new String[0];
		final VarList[] inParams = new VarList[0];
		final VarList[] outParams = new VarList[0];
		final Procedure proc = new Procedure(bl, attribute, "myProcedure", typeParams, inParams, outParams, modArray, body);
        decList.add(proc);
		final Declaration[] decArray = decList.toArray(new Declaration[decList.size()]);
        unit.setDeclarations(decArray);
        return unit;
  }  

    public void initBoogieLocations(int count) {
		if (inputFilePath == null) {
    		inputFilePath = boogieFilePath;
		}
    	boogieLocations = new BoogieLocation[count+1];
		boogieLocations[0] =
				new BoogieLocation(inputFilePath, 1, count, 0, 100, false);
    	for (int i= 0; i < count; i++) {
    		boogieLocations[i+1] =
    				new BoogieLocation(inputFilePath, i+1, i+1, 0, 100, false);
    	}
    }
    
    public PatternType getRequirement(int i){
    	return mRequirements[i];
    }
    
    public Unit genBoogie (PatternType[] patterns) {
		mRequirements = patterns;
		return genBoogie(new ReqToPEA().genPEA(patterns));
    }
    
	public Unit genBoogie (PhaseEventAutomata[] automata) {
		initBoogieLocations(automata.length);
 
        this.automata = automata;
		genGlobVars ();          
        return genProc();
	}
}
