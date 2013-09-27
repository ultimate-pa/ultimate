package pea_to_boogie.translator;
import java.util.*;

import pea.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.*;
import java.io.FileWriter;
import java.io.PrintWriter; 
import pea_to_boogie.generator.*;
/**
 * This class translates a phase event automaton to an equivalent Boogie code.
 */
public class Translator {

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
     * The list of state variables.
     */
    public List<String> stateVars = new ArrayList<String>();
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
     * The value of combinations of automata. 
     */
    public int combinationNum;
    /**
     * Assign an address to the boogieFilePath.  
     * @param The address of a Boogie text file.
     */
    public void setBoogieFilePath(String path) {
    	this.boogieFilePath = path;
    }
    /**
     * 
     * @return The address of a Boogie text file.
     */
    public String getBoogieFilePath() {
    	return this.boogieFilePath;
    }
    /**
     * Assign a value to the combinationNum.
     * @param num
     */
    public void setCombinationNum(int num) {
    	this.combinationNum = num;
    }
    /**
     * Generate global variables. 
     */
    public void genGlobVars() {
    	
       try {
          BoogieLocation blUnit = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, null);
          BoogieLocation blVar = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, blUnit);
          BoogieLocation blPrimType = new BoogieLocation (getBoogieFilePath(),
          		   0, 0, 0, 0, blVar);
         
          for (int i = 0; i < this.automata.length; i++) {
        	    List<String> tempClocks = this.automata[i].getClocks();
        	  for (int j = 0; j < tempClocks.size(); j++) {  
        	    this.clockIds.add(tempClocks.get(j));
              }            
          }
          ASTType astType = new PrimitiveType(blPrimType, "real"); 
          VarList clockVars = new VarList(blVar, this.clockIds.toArray(new String[this.clockIds.size()]),
          		  astType); 
          
          List<String> extraVars = new ArrayList<String>();
          for (int i = 0; i < this.automata.length; i++) {
        	  this.pcIds.add("pc"+i);
        	  extraVars.add("pc"+i);
          }
          astType = new PrimitiveType(blPrimType, "int");
          VarList pcVar = new VarList(blVar, extraVars.toArray(new String[extraVars.size()]),
        		  astType);
          
          boolean visited = false;
          for (int i = 0; i < this.automata.length; i++) {
        	  // System.out.println(this.automata[i].getVariables().size());

        	  Map<String, String> map = this.automata[i].getVariables();
    	    
      		  for( String name: map.keySet() ) {
    	    	  if (map.get(name).equals("boolean")){
    	    		  for (int j = 0; j < this.stateVars.size(); j++) { 
    	    			  if (name.equals(this.stateVars.get(j))) {
    	    				  visited = true;
    	    				  break;
    	    			  }
    	    		  }
    	    		  if (!visited) {
    	    			  this.stateVars.add(name);
    	    			  this.primedVars.add(name + "'");
    	    		  }
    	    	  } else if (map.get(name).equals("event")) {
    	    		  for (int j = 0; j < this.eventVars.size(); j++) { 
    	    			  if (name.equals(this.eventVars.get(j))) {
    	    				  visited = true;
    	    				  break;
    	    			  }
    	    		  }
    	    		  if (!visited) {
    	    			  this.eventVars.add(name);
    	    		  }
    	    	  }
    	    	  visited = false;
    	      } 
          }                          
          extraVars.clear();
          extraVars.add("delta");
          astType = new PrimitiveType(blPrimType, "real");
          VarList deltaVar = new VarList(blVar, extraVars.toArray(new String[extraVars.size()]),
        		  astType);
          List<VarList> varList = new ArrayList<VarList>();
          varList.add(clockVars);
          varList.add(pcVar);
          varList.add(deltaVar);
          
          if (this.stateVars.size() != 0) {
              astType = new PrimitiveType(blPrimType, "bool"); 
              List<String> stVarsList = new ArrayList<String>();
              for (int i = 0; i < this.stateVars.size(); i++) {
            	  stVarsList.add(this.stateVars.get(i));
            	  stVarsList.add(this.primedVars.get(i));
              }
              VarList stVars = new VarList(blVar, stVarsList.toArray(new String[stVarsList.size()]),
              		  astType); 
        	  varList.add(stVars);
          }
          
          if (this.eventVars.size() != 0) {
              astType = new PrimitiveType(blPrimType, "bool"); 
              VarList evVars = new VarList(blVar, this.eventVars.toArray(new String[this.eventVars.size()]),
              		  astType); 
        	  varList.add(evVars);
          }
          Attribute[] attribute = new Attribute[0];
          VariableDeclaration vars = new VariableDeclaration(blVar, attribute,
        		  varList.toArray(new VarList[varList.size()]));
          this.decList.add(vars);
          Declaration[]  decArray = this.decList.toArray(new Declaration[this.decList.size()]);
          this.unit = new Unit (blUnit, decArray);
       }
       catch (Exception e) {
    	   e.printStackTrace();
       }
    }
    /**
     * Generate the CNF of a list of expressions.
     * @param exprs: list of expressions.
     * @param bl: Boogie location. 
     * @return the CNF of a list of expressions.
     */
    public Expression genCNF (List<Expression> exprs, BoogieLocation bl) {
    	List<Expression> exprList = new ArrayList<Expression>();
    	for (int i = 0; i < exprs.size(); i++) {   		
      		if (exprList.size() == 0) {
                exprList.add(exprs.get(i));
      		} else {
      			BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND,
       	     			exprList.get(exprList.size()-1), exprs.get(i));
       	        exprList.add(binaryExpr);
      		}
  	    }
    	return exprList.get(exprList.size()-1);
    }
    /**
     * Generate time passing.
     * @param clock identifier.
     * @param Boogie location.
     * @return time passing statement. 
     */
    public Statement genClockPlusDelta(String clockId, BoogieLocation bl) {
    	BoogieLocation blAssign = new BoogieLocation (getBoogieFilePath(),
     		   0, 0, 0, 0, bl);
		BoogieLocation blLHS = new BoogieLocation (getBoogieFilePath(),
	      		   0, 0, 0, 0, blAssign);
	    BoogieLocation blRHS = new BoogieLocation (getBoogieFilePath(),
	       		   0, 0, 0, 0, blAssign);
	    VariableLHS clockVar = new VariableLHS(blLHS, clockId);
	    
		BoogieLocation blPlusLHS = new BoogieLocation (getBoogieFilePath(),
	      		   0, 0, 0, 0, blRHS);
	    BoogieLocation blPlusRHS = new BoogieLocation (getBoogieFilePath(),
	       		   0, 0, 0, 0, blRHS);	     	
	    IdentifierExpression clockID = new IdentifierExpression(blPlusLHS, clockId);
	    IdentifierExpression deltaID = new IdentifierExpression(blPlusRHS, "delta");
	    BinaryExpression binaryExpr = new BinaryExpression(blRHS, BinaryExpression.Operator.ARITHPLUS,
	    		clockID, deltaID);
	    LeftHandSide[] lhs = new LeftHandSide[1];
	    lhs[0] = clockVar;
	    Expression[] expr = new Expression[1];
	    expr[0] = binaryExpr;
	    AssignmentStatement assignment = new AssignmentStatement(blAssign, lhs, expr);
	    
    	return assignment;
    }
    public Statement[] genDelay(BoogieLocation bl) {
    	
    	BoogieLocation blVarsHavoc = new BoogieLocation (getBoogieFilePath(),
        		   0, 0, 0, 0, bl);
    	List<String> havocIds = new ArrayList<String>();
    	for (int i = 0; i < this.primedVars.size(); i++) {
    		havocIds.add(this.primedVars.get(i));
    	}
    	for (int i = 0; i < this.eventVars.size(); i++) {
    		havocIds.add(this.eventVars.get(i));
    	}
    	havocIds.add("delta");   	
     	String[] ids =  havocIds.toArray(new String[havocIds.size()]);
     	HavocStatement havocSmt = new HavocStatement(blVarsHavoc, ids);    	
     	BoogieLocation blDeltaAssume = new BoogieLocation (getBoogieFilePath(),
     		   0, 0, 0, 0, bl);
		BoogieLocation blLHS = new BoogieLocation (getBoogieFilePath(),
	      		   0, 0, 0, 0, blDeltaAssume);
	    BoogieLocation blRHS = new BoogieLocation (getBoogieFilePath(),
	       		   0, 0, 0, 0, blDeltaAssume);	     	
	    IdentifierExpression identifier = new IdentifierExpression(blLHS, "delta");
	    RealLiteral realLiteral = new RealLiteral(blRHS, Double.toString(0.0));
	    BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPGT,
	    		identifier, realLiteral);
    	AssumeStatement assumeDelta = new AssumeStatement(blDeltaAssume, binaryExpr);
    	
    	BoogieLocation blClockPlusDelta = new BoogieLocation (getBoogieFilePath(),
     		   0, 0, 0, 0, bl);
    	Statement[] smtArray = new Statement[this.clockIds.size()];
    	for (int i = 0; i < this.clockIds.size(); i++) {
    		smtArray[i] = genClockPlusDelta(this.clockIds.get(i), blClockPlusDelta);
    	}    	  	
    	Statement[] statements = new Statement[smtArray.length + 2];
    	statements[0] = havocSmt;
    	statements[1] = assumeDelta;
    	for (int i = 2; i < statements.length; i++) {

    		statements[i] = smtArray[i-2];
    	}
    	return statements;
    }
    public Expression genIfCons (int phaseIndex, int autIndex, BoogieLocation bl) {
    	BoogieLocation blConOperator = new BoogieLocation (getBoogieFilePath(),
        		   0, 0, 0, 0, bl);
    	BoogieLocation blLHS = new BoogieLocation (getBoogieFilePath(),
     		   0, 0, 0, 0, blConOperator);
    	BoogieLocation blRHS = new BoogieLocation (getBoogieFilePath(),
      		   0, 0, 0, 0, blConOperator);
    	
    	IdentifierExpression identifier = new IdentifierExpression(blLHS, "pc"+autIndex);
    	IntegerLiteral intLiteral = new IntegerLiteral(blRHS, 
    			Integer.toString(phaseIndex));
    	BinaryExpression ifCon = new BinaryExpression(blConOperator, BinaryExpression.Operator.COMPEQ,
    			identifier, intLiteral);
    	return ifCon;
    }
    public Statement[] genIfSmtDelayBody(Phase phase, BoogieLocation bl) {
     	BoogieLocation blAssumeClInv = new BoogieLocation (getBoogieFilePath(),
      		   0, 0, 0, 0, bl);
     	BoogieLocation blAssumeStateInv = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, bl);     	
 	    Expression expr	= new CDDTranslator().CDD_To_Boogie(phase.getClockInvariant(),getBoogieFilePath(), blAssumeClInv);
     	AssumeStatement assumeClInv = new AssumeStatement(blAssumeClInv, expr);
     	expr = new CDDTranslator().CDD_To_Boogie(phase.getStateInvariant(),getBoogieFilePath(), blAssumeStateInv);
     	AssumeStatement assumeStateInv = new AssumeStatement(blAssumeStateInv, expr);
     	Statement[] statements = new Statement[2];
    	statements[0] = assumeClInv;
    	statements[1] = assumeStateInv;
    	return statements;
    }
    public Statement joinIfSmts (Statement[] statements, BoogieLocation bl) {
    	
    	List<Statement> smtList = new ArrayList<Statement>();
    	BoogieLocation blIfSmt = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, bl);
    	for (int i = 0; i < statements.length; i++) {
    		IfStatement oldIfSmt = (IfStatement)statements[i];
    		if (smtList.size() == 0) {
    	     Statement[] emptyArray = new Statement[0];
           	 IfStatement newIfSmt = new IfStatement(blIfSmt, oldIfSmt.getCondition(), 
           			  oldIfSmt.getThenPart(), emptyArray);	
           	smtList.add(newIfSmt);
    		} else {
    			Statement[] smt = new Statement[1];
    			smt[0] = smtList.get(smtList.size()-1);
              	IfStatement newIfSmt = new IfStatement(blIfSmt, oldIfSmt.getCondition(), 
              			  oldIfSmt.getThenPart(), smt);
              	smtList.add(newIfSmt);
    		}
    	}
    	  
    	return smtList.get(smtList.size()-1);
    }
    public Statement joinInnerIfSmts (Statement[] statements, BoogieLocation bl) {
    	
    	List<Statement> smtList = new ArrayList<Statement>();
    	BoogieLocation blIfSmt = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, bl);
    	for (int i = 0; i < statements.length; i++) {
    		IfStatement oldIfSmt = (IfStatement)statements[i];
    		if (smtList.size() == 0) {
    	     BoogieLocation blAssumeFalse = new BoogieLocation (getBoogieFilePath(),
    	       		   0, 0, 0, 0, bl);
    	     BooleanLiteral bLiteral = new BooleanLiteral(blAssumeFalse, false);
    	     AssumeStatement assumeFalse = new AssumeStatement(blAssumeFalse, bLiteral);	
    	     Statement[] smt = new Statement[1];
    	     smt[0] = assumeFalse;
    	     IfStatement newIfSmt = new IfStatement(blIfSmt, oldIfSmt.getCondition(), 
           			  oldIfSmt.getThenPart(), smt);	
           	smtList.add(newIfSmt);
    		} else {
    			Statement[] smt = new Statement[1];
    			smt[0] = smtList.get(smtList.size()-1);
              	IfStatement newIfSmt = new IfStatement(blIfSmt, oldIfSmt.getCondition(), 
              			  oldIfSmt.getThenPart(), smt);
              	smtList.add(newIfSmt);
    		}
    	}
    	  
    	return smtList.get(smtList.size()-1);
    }
    public Statement genIfSmtDelay(PhaseEventAutomata automaton, int autIndex, BoogieLocation bl) {
    	
    	Phase[] phases = automaton.getPhases();
    	Statement[] statements = new Statement[phases.length];
    	for (int i = 0; i < phases.length; i++) {
    	  BoogieLocation blIfSmt = new BoogieLocation (getBoogieFilePath(),
        		   0, 0, 0, 0, bl);
     	  BoogieLocation blIfStmCon = new BoogieLocation (getBoogieFilePath(),
         		   0, 0, 0, 0, bl);
     	  Expression ifCon = genIfCons(i, autIndex, blIfStmCon);
     	  Statement [] emptyArray = new Statement[0];
     	  IfStatement ifStatement = new IfStatement(blIfSmt, ifCon, 
     			  genIfSmtDelayBody(phases[i],bl), emptyArray);
     	 statements[i] = ifStatement;
    	}
    	Statement statement = joinIfSmts(statements, bl);
    	return statement;
    }
    public Statement genReset(String resetVar, BoogieLocation bl) {
    	BoogieLocation blAssign = new BoogieLocation (getBoogieFilePath(),
     		   0, 0, 0, 0, bl);
		BoogieLocation blLHS = new BoogieLocation (getBoogieFilePath(),
	      		   0, 0, 0, 0, blAssign);
	    BoogieLocation blRHS = new BoogieLocation (getBoogieFilePath(),
	       		   0, 0, 0, 0, blAssign);
	    VariableLHS reset = new VariableLHS(blLHS, resetVar);
     	
    	RealLiteral realLiteral = new RealLiteral(blRHS, 
    			Double.toString(0.0));
	    LeftHandSide[] lhs = new LeftHandSide[1];
	    lhs[0] = reset;
	    Expression[] expr = new Expression[1];
	    expr[0] = realLiteral;
	    AssignmentStatement assignment = new AssignmentStatement(blAssign, lhs, expr);
	    
    	return assignment;
    }
    public Statement genPCAssign(int autIndex, int phaseIndex, BoogieLocation bl) {
    	BoogieLocation blAssign = new BoogieLocation (getBoogieFilePath(),
     		   0, 0, 0, 0, bl);
		BoogieLocation blLHS = new BoogieLocation (getBoogieFilePath(),
	      		   0, 0, 0, 0, blAssign);
	    BoogieLocation blRHS = new BoogieLocation (getBoogieFilePath(),
	       		   0, 0, 0, 0, blAssign);
	    VariableLHS pc = new VariableLHS(blLHS, "pc"+autIndex);
     	
    	IntegerLiteral intLiteral = new IntegerLiteral(blRHS, 
    			Integer.toString(phaseIndex));
	    LeftHandSide[] lhs = new LeftHandSide[1];
	    lhs[0] = pc;
	    Expression[] expr = new Expression[1];
	    expr[0] = intLiteral;
	    AssignmentStatement assignment = new AssignmentStatement(blAssign, lhs, expr);
	    
    	return assignment;
    }

    public Statement[] genInnerIfBody(PhaseEventAutomata automaton, Transition transition, 
    		int autIndex, BoogieLocation bl) {
           	
    	List<Statement> smtList = new ArrayList<Statement>();
    	BoogieLocation blAssumeGuard = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, bl);      	
    //	StringLiteral strLiteral = new StringLiteral(blAssumeGuard, 
  	//    		CDDTranslation.CDD_To_Boogie(transition.getGuard()));
    	Expression expr	= new CDDTranslator().CDD_To_Boogie(transition.getGuard(),getBoogieFilePath(),
    			blAssumeGuard);
      	AssumeStatement assumeGuard = new AssumeStatement(blAssumeGuard, expr);     	 
      	smtList.add(assumeGuard);
        if (transition.getResets().length != 0) {
        	String[] resets = transition.getResets();
        	for (int i = 0; i < resets.length; i++) {
        		smtList.add(genReset(resets[i], bl));
        	} 
        }
        Phase desPhase = transition.getDest();
        Phase[] phases = automaton.getPhases();
        int phaseIndex = -1;
        for (int i = 0; i < phases.length; i++) {
        	if (phases[i].getName().equals(desPhase.getName())) phaseIndex = i;
        }
        smtList.add(genPCAssign(autIndex, phaseIndex, bl));
        
        Statement[] statements = smtList.toArray(new Statement[smtList.size()]);
    	return statements;
    }
    
    public Statement genOuterIfBody(PhaseEventAutomata automaton, Phase phase, int autIndex, BoogieLocation bl) {
    	
    	Statement[] statements = new Statement[phase.getTransitions().size()];
    	List<Transition> transitions = phase.getTransitions();
    	for (int i = 0; i < transitions.size(); i++) {
      	  BoogieLocation blIfSmt = new BoogieLocation (getBoogieFilePath(),
          		   0, 0, 0, 0, bl);
       	  BoogieLocation blIfStmCon = new BoogieLocation (getBoogieFilePath(),
           		   0, 0, 0, 0, bl);
          WildcardExpression wce = new WildcardExpression(blIfStmCon);
       	  Statement[] emptyArray = new Statement[0];
       	  IfStatement ifStatement = new IfStatement(blIfSmt, wce, 
       			 genInnerIfBody(automaton, transitions.get(i), autIndex, bl), emptyArray);
       	 statements[i] = ifStatement;
      	}
    	Statement statement = joinInnerIfSmts(statements, bl);
    	
    	return statement;
    } 
    public Statement genOuterIfTransition(PhaseEventAutomata automaton, int autIndex, BoogieLocation bl) {
	   	
    	Phase[] phases = automaton.getPhases();
    	Statement[] statements = new Statement[phases.length];
    	for (int i = 0; i < phases.length; i++) {
    	  BoogieLocation blIfSmt = new BoogieLocation (getBoogieFilePath(),
        		   0, 0, 0, 0, bl);
     	  BoogieLocation blIfStmCon = new BoogieLocation (getBoogieFilePath(),
         		   0, 0, 0, 0, bl);
     	  Expression ifCon = genIfCons(i, autIndex, blIfStmCon);
     	  Statement[] emptyArray = new Statement[0];
     	  Statement[] outerIfBodySmt = new Statement[1];
     	  outerIfBodySmt[0] = genOuterIfBody(automaton, phases[i], autIndex, bl);
     	  IfStatement ifStatement = new IfStatement(blIfSmt, ifCon, 
     			 outerIfBodySmt, emptyArray);
     	 statements[i] = ifStatement;
    	}
    	Statement statement = joinIfSmts(statements, bl);
    	
    	return statement;
    }
    public List<Statement> genStateVarsAssign(BoogieLocation bl){
      List<Statement> statements = new ArrayList<Statement>();
      for(int i = 0; i < this.stateVars.size(); i++) { 
    	BoogieLocation blAssign = new BoogieLocation (getBoogieFilePath(),
      		   0, 0, 0, 0, bl);
 		BoogieLocation blLHS = new BoogieLocation (getBoogieFilePath(),
 	      		   0, 0, 0, 0, blAssign);
 	    BoogieLocation blRHS = new BoogieLocation (getBoogieFilePath(),
 	       		   0, 0, 0, 0, blAssign);
 	    VariableLHS lhsVar = new VariableLHS(blLHS, this.stateVars.get(i));
    	IdentifierExpression rhs = new IdentifierExpression(blRHS, this.primedVars.get(i));
 	    LeftHandSide[] lhs = new LeftHandSide[1];
 	    lhs[0] = lhsVar;
	    Expression[] expr = new Expression[1];
	    expr[0] = rhs;
 	    AssignmentStatement assignment = new AssignmentStatement(blAssign, lhs, expr);
 	    statements.add(assignment);
      }
    	return statements;
    }
    public Statement genAssertSmt(List<Integer> permutation, BoogieLocation bl) {
     	BoogieLocation blAssert = new BoogieLocation (getBoogieFilePath(),
      		   0, 0, 0, 0, bl);
     	ConditionGenerator conGen = new ConditionGenerator();
     	conGen.setTranslator(this);
     	Expression expr = conGen.nonDLCGenerator(this.automata, permutation, 
     			getBoogieFilePath(), blAssert);
     	if (expr == null) return null;
 	    AssertStatement assertSmt = new AssertStatement(blAssert, expr);
    	return assertSmt;
    }
    /**
     * @param bl
     *       Location of the while statement.
     * @return
     *        Statements of the while-body.
     */
    public Statement[] genWhileBody (BoogieLocation bl) {
    	List<Statement> smtList = new ArrayList<Statement>();        
    	Statement[] delaySmts = genDelay(bl); 
    	for (int i = 0; i < delaySmts.length; i++) {
    		smtList.add(delaySmts[i]);
    	}
       
    	for (int i = 0; i < this.automata.length; i++) {    
    	    smtList.add(genIfSmtDelay(this.automata[i], i, bl));   	    
    	}
    	List<Integer> myList = new ArrayList<Integer>(); 
    	for(int i = 0; i < this.automata.length; i++) {
    		myList.add(i);
    	}
    	List<List<Integer>> permutation = new Permutation().permutation(myList, this.combinationNum);
/*
		for (int i = 0; i < permutation.size(); i++) {
			 myList = permutation.get(i);   		
			for(int j = 0; j < myList.size(); j++) {
				System.out.println(myList.get(j));
			}
			System.out.println("////////////////////////////////////////////");
		}
*/      for (int i = 0; i < permutation.size(); i++) {
    	 Statement assertSmt = genAssertSmt(permutation.get(i), bl);
    	 if (assertSmt == null) continue;
    	 smtList.add(assertSmt);
        }
    	for (int i = 0; i < this.automata.length; i++) { 
    	    smtList.add(genOuterIfTransition(this.automata[i], i, bl));   	    
    	}
   	    if (this.stateVars.size() != 0) {
   	    	List<Statement> stateVarsAssigns = genStateVarsAssign(bl);
   	    	for (int i = 0; i < stateVarsAssigns.size(); i++) {
   	    		smtList.add(stateVarsAssigns.get(i));
   	    	} 
   	    }
    	
    	Statement[] statements = smtList.toArray(new Statement[smtList.size()]);
    	return statements;
    }
    /**
     * The while-statement is initialized. 
     * @param bl
     *          Location of the procedure body.
     * @return
     *        The while-statement.
     */
    public Statement genWhileSmt (BoogieLocation bl) {
    	BoogieLocation blWhile = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, bl);
          	    	
    	BoogieLocation blWildcardExp = new BoogieLocation (getBoogieFilePath(),
        		   0, 0, 0, 0, blWhile);
    	WildcardExpression wce = new WildcardExpression(blWildcardExp);
    	LoopInvariantSpecification[] invariants = new LoopInvariantSpecification[0];
    	WhileStatement whileStatement = new WhileStatement(blWhile, wce,invariants, 
    			genWhileBody (blWhile));
    	return whileStatement;
    }
    public Expression genPcExpr(Phase[] phases,Phase[] initialPhases, int autIndex, BoogieLocation bl) {
    	List<Expression> exprList = new ArrayList<Expression>();
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
    		BoogieLocation blLHS = new BoogieLocation (getBoogieFilePath(),
 	      		   0, 0, 0, 0, bl);
 	     	BoogieLocation blRHS = new BoogieLocation (getBoogieFilePath(),
 	       		   0, 0, 0, 0, bl);	     	
 	     	IdentifierExpression identifier = new IdentifierExpression(blLHS, "pc"+autIndex);
 	     	IntegerLiteral intLiteral = new IntegerLiteral(blRHS, Integer.toString(i));
 	     	BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ,
 	     			identifier, intLiteral);
    		if (exprList.size() == 0) {
              exprList.add(binaryExpr);
    		} else {
    	    	blLHS = new BoogieLocation (getBoogieFilePath(),
    	 	      		   0, 0, 0, 0, bl);
    	 	    blRHS = new BoogieLocation (getBoogieFilePath(),
    	 	       		   0, 0, 0, 0, bl);
     	        binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR,
     	     			exprList.get(exprList.size()-1), binaryExpr);
     	        exprList.add(binaryExpr);
    		}
	      }
    	}
    	return exprList.get(exprList.size()-1);
    } 
    public Statement[] genInitialPhasesSmts (BoogieLocation bl) {
    	BoogieLocation blPCHavoc = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, bl);
    	String[] ids = new String[this.pcIds.size()];
    	for (int i = 0; i < this.pcIds.size(); i++) {
    		ids[i] = this.pcIds.get(i);
    	}
    	HavocStatement pcHavoc = new HavocStatement(blPCHavoc, ids);
    	
    	BoogieLocation blPCassume = new BoogieLocation (getBoogieFilePath(),
        		   0, 0, 0, 0, bl);

    	List<Expression> pcExprs = new ArrayList<Expression>();
    	for (int i = 0; i < this.automata.length; i++) {
    		pcExprs.add(genPcExpr(this.automata[i].getPhases(), this.automata[i].getInit(), i, blPCassume));
    	}
    	
    	AssumeStatement assumeSmt = new AssumeStatement(blPCassume, genCNF(pcExprs, blPCassume));
    	
    	Statement[] statements = new Statement[2];
    	statements[0] = pcHavoc;
    	statements[1] = assumeSmt;
    	return statements;
    }
    public Expression genClockInit (BoogieLocation bl) {
    	List<Expression> exprList = new ArrayList<Expression>();
    	BoogieLocation blClockExpr = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, bl);
    	for (int i = 0; i < this.clockIds.size(); i++) {
	    	BoogieLocation blLHS = new BoogieLocation (getBoogieFilePath(),
 	      		   0, 0, 0, 0, blClockExpr);
 	     	BoogieLocation blRHS = new BoogieLocation (getBoogieFilePath(),
 	       		   0, 0, 0, 0, blClockExpr);	     	
 	     	IdentifierExpression identifier = new IdentifierExpression(blLHS, this.clockIds.get(i));
 	     	RealLiteral realLiteral = new RealLiteral(blRHS, Double.toString(0));
 	     	BinaryExpression binaryExpr = new BinaryExpression(blClockExpr, BinaryExpression.Operator.COMPEQ,
 	     			identifier, realLiteral);
    		if (exprList.size() == 0) {
              exprList.add(binaryExpr);
    		} else {
    	    	blLHS = new BoogieLocation (getBoogieFilePath(),
    	 	      		   0, 0, 0, 0, blClockExpr);
    	 	    blRHS = new BoogieLocation (getBoogieFilePath(),
    	 	       		   0, 0, 0, 0, blClockExpr);
     	        binaryExpr = new BinaryExpression(blClockExpr, BinaryExpression.Operator.LOGICAND,
     	     			exprList.get(exprList.size()-1), binaryExpr);
     	        exprList.add(binaryExpr);
    		}
    	}

    	return exprList.get(exprList.size()-1);
    }
    public Statement[] genClockInitSmts (BoogieLocation bl) { 
    	BoogieLocation blClockHavoc = new BoogieLocation (getBoogieFilePath(),
        		   0, 0, 0, 0, bl);
     	HavocStatement clockHavoc = new HavocStatement(blClockHavoc, 
     			this.clockIds.toArray(new String[this.clockIds.size()]));
     	
     	BoogieLocation blClockAssume = new BoogieLocation (getBoogieFilePath(),
         		   0, 0, 0, 0, bl);
     	AssumeStatement assumeSmt = new AssumeStatement(blClockAssume, genClockInit(blClockAssume));
     	
     	Statement[] statements = new Statement[2];
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
     
    	Statement[] initPhasesSmts = genInitialPhasesSmts (bl);
    	Statement[] clockInitSmts = genClockInitSmts (bl);
    	Statement whileStatement = genWhileSmt(bl);    	
    	Statement[] statements = new Statement[5];
        statements[0] = initPhasesSmts[0];
        statements[1] = initPhasesSmts[1];
        statements[2] = clockInitSmts [0];
        statements[3] = clockInitSmts [1];
        statements[4] = whileStatement;
    	return statements;
    }
    /**
     * The procedure statement is initialized. It is deployed to the unit.
     * The unit is sent to the print process. The result is a Boogie text file. 
     */
    public Unit genProc () {
    	BoogieLocation blProc = new BoogieLocation (getBoogieFilePath(),
     		   0, 0, 0, 0, unit.getLocation());
        
        BoogieLocation blModifies = new BoogieLocation (getBoogieFilePath(),
       		   0, 0, 0, 0, blProc);
        
        BoogieLocation blProcBody = new BoogieLocation (getBoogieFilePath(),
     		   0, 0, 0, 0, blProc);       
        VariableDeclaration[] localVars = new VariableDeclaration[0];
        Body body = new Body(blProcBody, localVars, genProcBodySmts (blProcBody));         
        List<String> modifiedVarsList = new ArrayList<String>();
        for (int i = 0; i < this.clockIds.size(); i++) {
        	modifiedVarsList.add(this.clockIds.get(i));
        }
        for (int i = 0; i < this.pcIds.size(); i++) {
        	modifiedVarsList.add(this.pcIds.get(i));
        }
        modifiedVarsList.add("delta");
        
        for (int i = 0; i < this.stateVars.size(); i++) {
        	modifiedVarsList.add(this.stateVars.get(i));
        	modifiedVarsList.add(this.primedVars.get(i));
        }
        
        for (int i = 0; i < this.eventVars.size(); i++) {
        	modifiedVarsList.add(this.eventVars.get(i));
        }
        String[] modifiedVars = new String[modifiedVarsList.size()];
        for (int i = 0; i < modifiedVars.length; i++) {
        	modifiedVars[i] = modifiedVarsList.get(i);
        }       
        ModifiesSpecification mod = new ModifiesSpecification(blModifies, false, modifiedVars);
        ModifiesSpecification[] modArray = new ModifiesSpecification[1];
        modArray[0] = mod;
        Attribute[] attribute = new Attribute[0];
        String[] typeParams = new String[0];
        VarList[] inParams = new VarList[0];
        VarList[] outParams = new VarList[0];
        Procedure proc = new Procedure(blProc, attribute, "myProcedure", typeParams, inParams, outParams, modArray, body);
        decList.add(proc);
        Declaration[] decArray = decList.toArray(new Declaration[decList.size()]); 
        unit.setDeclarations(decArray);
        return unit;
  }  

	public Unit genBoogie (PhaseEventAutomata[] automata) {
 
        this.automata = automata;
		genGlobVars ();          
        return genProc();
	} 	

}
