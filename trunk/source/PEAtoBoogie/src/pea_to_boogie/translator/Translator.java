/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package pea_to_boogie.translator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import pea.Phase;
import pea.PhaseBits;
import pea.PhaseEventAutomata;
import pea.Transition;
import pea_to_boogie.generator.ConditionGenerator;
import pea_to_boogie.generator.Permutation;
import req_to_pea.ReqToPEA;
import srParse.srParsePattern;

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
	public List<Declaration> decList = new ArrayList<>();
	/**
	 * The list of clock identifiers.
	 */
	public List<String> clockIds = new ArrayList<>();
	/**
	 * The list of unique identifiers. Each identifier is in the form of "pc" + phaseIndex. Each automaton has an array
	 * of phases. The location of each phase in that array specifies the value of phaseIndex.
	 */
	public List<String> pcIds = new ArrayList<>();
	/**
	 * The list of state variables.
	 */
	public List<String> stateVars = new ArrayList<>();
	/**
	 * The list of primed variables.
	 */
	public List<String> primedVars = new ArrayList<>();
	/**
	 * The list of events.
	 */
	public List<String> eventVars = new ArrayList<>();
	/**
	 * The list of automata.
	 */
	public PhaseEventAutomata[] automata;
	/**
	 * The array of input requirements.
	 */
	public srParsePattern[] mRequirements;
	
	/**
	 * The properties for which we check for vacuity.
	 */
	public BitSet mVacuityChecks;
	/**
	 * The value of combinations of automata.
	 */
	public int combinationNum;
	
	/**
	 * The boogie locations used to annotate the boogie code. This array contains the location for requirement reqNr in
	 * index reqNr+1 and the location for code that is not specific to any requirements in index 0.
	 */
	public BoogieLocation[] boogieLocations;
	
	private ILogger mLogger;
	
	public Translator(ILogger logger){
		mLogger = logger;
	}
	
	/**
	 * Set the input file name. This is used to annotate the Boogie code with the right file name. The Location object
	 * should contain the name of the original file name.
	 * 
	 * @param The
	 *            input file name.
	 */
	public void setInputFilePath(final String path) {
		inputFilePath = path;
	}
	
	public String getInputFilePath() {
		return inputFilePath;
	}
	
	/**
	 * Assign an address to the boogieFilePath.
	 * 
	 * @param The
	 *            address of a Boogie text file.
	 */
	public void setBoogieFilePath(final String path) {
		boogieFilePath = path;
	}
	
	/**
	 * @return The address of a Boogie text file.
	 */
	public String getBoogieFilePath() {
		return boogieFilePath;
	}
	
	/**
	 * Add a bitset containing the numbers of the components for which vacuity should be checked.
	 * 
	 * @param vacuityChecks
	 *            the bitset. Bit i is set if we should check vacuity for the i-th property.
	 */
	public void setVacuityChecks(final BitSet vacuityChecks) {
		mVacuityChecks = vacuityChecks;
	}
	
	public boolean checkVacuity(final int propertyNum) {
		return mVacuityChecks != null && mVacuityChecks.get(propertyNum);
	}
	
	/**
	 * Assign a value to the combinationNum.
	 * 
	 * @param num
	 */
	public void setCombinationNum(final int num) {
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
			
			final List<String> extraVars = new ArrayList<>();
			for (int i = 0; i < automata.length; i++) {
				pcIds.add("pc" + i);
				extraVars.add("pc" + i);
			}
			astType = new PrimitiveType(blPrimType, "int");
			final VarList pcVar = new VarList(blVar, extraVars.toArray(new String[extraVars.size()]), astType);
			
			boolean visited = false;
			for (int i = 0; i < automata.length; i++) {
				// System.out.println(this.automata[i].getVariables().size());
				
				final Map<String, String> map = automata[i].getVariables();
				
				for (final String name : map.keySet()) {
					if (map.get(name).equals("boolean")) {
						for (int j = 0; j < stateVars.size(); j++) {
							if (name.equals(stateVars.get(j))) {
								visited = true;
								break;
							}
						}
						if (!visited) {
							stateVars.add(name);
							primedVars.add(name + "'");
						}
					} else if (map.get(name).equals("event")) {
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
			final List<VarList> varList = new ArrayList<>();
			if (!clockIds.isEmpty()) {
				varList.add(clockVars);
			}
			varList.add(pcVar);
			varList.add(deltaVar);
			
			if (!stateVars.isEmpty()) {
				astType = new PrimitiveType(blPrimType, "bool");
				final List<String> stVarsList = new ArrayList<>();
				for (int i = 0; i < stateVars.size(); i++) {
					stVarsList.add(stateVars.get(i));
					stVarsList.add(primedVars.get(i));
				}
				final VarList stVars = new VarList(blVar, stVarsList.toArray(new String[stVarsList.size()]), astType);
				varList.add(stVars);
			}
			
			if (!eventVars.isEmpty()) {
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
	 * 
	 * @param exprs
	 *            list of expressions.
	 * @param bl
	 *            Boogie location.
	 * @return the CNF of a list of expressions.
	 */
	public static Expression genConjunction(final List<Expression> exprs, final BoogieLocation bl) {
		final Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext()) {
			return new BooleanLiteral(bl, true);
		}
		Expression cnf = it.next();
		while (it.hasNext()) {
			cnf = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND, cnf, it.next());
		}
		return cnf;
	}
	
	/**
	 * Generate the disjunction of a list of expressions.
	 * 
	 * @param exprs
	 *            list of expressions.
	 * @param bl
	 *            Boogie location.
	 * @return the CNF of a list of expressions.
	 */
	public static Expression genDisjunction(final List<Expression> exprs, final BoogieLocation bl) {
		final Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext()) {
			return new BooleanLiteral(bl, false);
		}
		Expression cnf = it.next();
		while (it.hasNext()) {
			cnf = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR, cnf, it.next());
		}
		return cnf;
	}
	
	/**
	 * Generate time passing.
	 * 
	 * @param clock
	 *            identifier.
	 * @param Boogie
	 *            location.
	 * @return time passing statement.
	 */
	public static Statement genClockPlusDelta(final String clockId, final BoogieLocation bl) {
		final VariableLHS clockVar = new VariableLHS(bl, clockId);
		
		final IdentifierExpression clockID = new IdentifierExpression(bl, clockId);
		final IdentifierExpression deltaID = new IdentifierExpression(bl, "delta");
		final BinaryExpression binaryExpr =
				new BinaryExpression(bl, BinaryExpression.Operator.ARITHPLUS, clockID, deltaID);
		final LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = clockVar;
		final Expression[] expr = new Expression[1];
		expr[0] = binaryExpr;
		final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
		
		return assignment;
	}
	
	/**
	 * Generate the delay statements and havoc all primed variables and event variables. The code has the form
	 * 
	 * <pre>
	 * 	   havoc primedVars, eventVars, delta;
	 *     assume delta > 0.0
	 *     clock1 := clock + delta;
	 *     ...
	 * </pre>
	 * 
	 * @param bl
	 * @return
	 */
	public Statement[] genDelay(final BoogieLocation bl) {
		
		final List<VariableLHS> havocIds = new ArrayList<>();
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
		System.arraycopy(smtArray, 0, statements, 2, smtArray.length);
		return statements;
	}
	
	/**
	 * Generate the expression <code>pc<i>autIndex</i> == <i>phaseIndex</i></code> that checks if the automaton autIndex
	 * is currently in the phase phaseIndex.
	 * 
	 * @param phaseIndex
	 *            the index of the phase we check for.
	 * @param autIndex
	 *            the index of the automaton.
	 * @param bl
	 * @return
	 */
	public static Expression genComparePhaseCounter(final int phaseIndex, final int autIndex, final BoogieLocation bl) {
		final IdentifierExpression identifier = new IdentifierExpression(bl, "pc" + autIndex);
		final IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(phaseIndex));
		final BinaryExpression ifCon =
				new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier, intLiteral);
		return ifCon;
	}
	
	/**
	 * Creates the code that checks the phase invariant of the given phase.
	 * 
	 * @param phase
	 *            the phase whose invariant should be checked.
	 * @param bl
	 * @return the array of (two) statements that check the invariant.
	 */
	public Statement[] genCheckPhaseInvariant(final Phase phase, final BoogieLocation bl) {
		Expression expr = new CDDTranslator().CDD_To_Boogie(phase.getClockInvariant(), getBoogieFilePath(), bl);
		final AssumeStatement assumeClInv = new AssumeStatement(bl, expr);
		expr = new CDDTranslator().CDD_To_Boogie(phase.getStateInvariant(), getBoogieFilePath(), bl);
		final AssumeStatement assumeStateInv = new AssumeStatement(bl, expr);
		final Statement[] statements = new Statement[2];
		statements[0] = assumeClInv;
		statements[1] = assumeStateInv;
		return statements;
	}
	
	public static Statement joinIfSmts(final Statement[] statements, final BoogieLocation bl) {
		
		final List<Statement> smtList = new ArrayList<>();
		for (int i = 0; i < statements.length; i++) {
			final IfStatement oldIfSmt = (IfStatement) statements[i];
			if (smtList.isEmpty()) {
				final Statement[] emptyArray = new Statement[0];
				final IfStatement newIfSmt =
						new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), emptyArray);
				smtList.add(newIfSmt);
			} else {
				final Statement[] smt = new Statement[1];
				smt[0] = smtList.get(smtList.size() - 1);
				final IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
				smtList.add(newIfSmt);
			}
		}
		
		return smtList.get(smtList.size() - 1);
	}
	
	public static Statement joinInnerIfSmts(final Statement[] statements, final BoogieLocation bl) {
		
		final List<Statement> smtList = new ArrayList<>();
		for (int i = 0; i < statements.length; i++) {
			final IfStatement oldIfSmt = (IfStatement) statements[i];
			if (smtList.isEmpty()) {
				final BooleanLiteral bLiteral = new BooleanLiteral(bl, false);
				final AssumeStatement assumeFalse = new AssumeStatement(bl, bLiteral);
				final Statement[] smt = new Statement[1];
				smt[0] = assumeFalse;
				final IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
				smtList.add(newIfSmt);
			} else {
				final Statement[] smt = new Statement[1];
				smt[0] = smtList.get(smtList.size() - 1);
				final IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
				smtList.add(newIfSmt);
			}
		}
		
		return smtList.get(smtList.size() - 1);
	}
	
	/**
	 * Check the invariants of the given automaton. This is an if statement that first checks in which phase the
	 * automaton is and then checks the corresponding invariants.
	 * 
	 * @param automaton
	 *            the automaton to check.
	 * @param autIndex
	 *            the index of the automaton to check.
	 * @param bl
	 *            The location information to correspond the generated source to the property.
	 * @return The if statement checking the p
	 */
	public Statement genCheckInvariants(final PhaseEventAutomata automaton, final int autIndex,
			final BoogieLocation bl) {
		
		final Phase[] phases = automaton.getPhases();
		final Statement[] statements = new Statement[phases.length];
		for (int i = 0; i < phases.length; i++) {
			final Expression ifCon = genComparePhaseCounter(i, autIndex, bl);
			final Statement[] emptyArray = new Statement[0];
			final IfStatement ifStatement =
					new IfStatement(bl, ifCon, genCheckPhaseInvariant(phases[i], bl), emptyArray);
			statements[i] = ifStatement;
		}
		final Statement statement = joinIfSmts(statements, bl);
		return statement;
	}
	
	public static Statement genReset(final String resetVar, final BoogieLocation bl) {
		final VariableLHS reset = new VariableLHS(bl, resetVar);
		
		final RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0.0));
		final LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = reset;
		final Expression[] expr = new Expression[1];
		expr[0] = realLiteral;
		final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
		
		return assignment;
	}
	
	public static Statement genPCAssign(final int autIndex, final int phaseIndex, final BoogieLocation bl) {
		final VariableLHS pc = new VariableLHS(bl, "pc" + autIndex);
		
		final IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(phaseIndex));
		final LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = pc;
		final Expression[] expr = new Expression[1];
		expr[0] = intLiteral;
		final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
		
		return assignment;
	}
	
	public Statement[] genInnerIfBody(final PhaseEventAutomata automaton, final Transition transition,
			final int autIndex,
			final BoogieLocation bl) {
		
		final List<Statement> smtList = new ArrayList<>();
		// StringLiteral strLiteral = new StringLiteral(blAssumeGuard,
		// CDDTranslation.CDD_To_Boogie(transition.getGuard()));
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
	
	public Statement genOuterIfBody(final PhaseEventAutomata automaton, final Phase phase, final int autIndex,
			final BoogieLocation bl) {
		
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
	
	public Statement genOuterIfTransition(final PhaseEventAutomata automaton, final int autIndex,
			final BoogieLocation bl) {
		
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
	
	public List<Statement> genStateVarsAssign(final BoogieLocation bl) {
		final List<Statement> statements = new ArrayList<>();
		for (int i = 0; i < stateVars.size(); i++) {
			final VariableLHS lhsVar = new VariableLHS(bl, stateVars.get(i));
			final IdentifierExpression rhs = new IdentifierExpression(bl, primedVars.get(i));
			final LeftHandSide[] lhs = new LeftHandSide[1];
			lhs[0] = lhsVar;
			final Expression[] expr = new Expression[1];
			expr[0] = rhs;
			final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
			statements.add(assignment);
		}
		return statements;
	}
	
	public Statement genAssertRTInconsistency(final int[] permutation, final BoogieLocation bl) {
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
	
	private Statement genAssertConsistency(final BoogieLocation bl) {
		final ReqCheck check = new ReqCheck(ReqCheck.ReqSpec.CONSISTENCY, new int[] { 0 }, this);
		final ReqLocation loc = new ReqLocation(check);
		return new AssertStatement(loc, new BooleanLiteral(bl, false));
	}
	
	/**
	 * Generate the assertion that is violated if the requirement represented by the given automaton is non-vacuous. The
	 * assertion expresses that the automaton always stays in the early phases and never reaches the last phase. It may
	 * be false if all phases of the automaton are part of the last phase, in which case this function returns null.
	 * 
	 * @param pea
	 *            The automaton for which vacuity is checked.
	 * @param automatonIndex
	 *            The number of the automaton.
	 * @param bl
	 *            A boogie location used for all statements.
	 * @return The assertion for non-vacousness or null if the assertion would be false.
	 */
	private Statement genAssertNonVacuous(final PhaseEventAutomata pea, final int automatonIndex,
			final BoogieLocation bl) {
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
		final List<Expression> checkReached = new ArrayList<>();
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
	 * Create the statements of the main loop of the pea product. The main loop looks like this
	 * 
	 * <pre>
	 *    delay statements (havoc delay, eventVar, primedVars, add delay to all clocks)
	 *    check invariants of phases
	 *    assert reachability
	 *    check transitions
	 * </pre>
	 * 
	 * @param bl
	 *            Location of the procedure body.
	 * @return Statements of the while-body.
	 */
	public Statement[] genWhileBody(final BoogieLocation bl) {
		final List<Statement> stmtList = new ArrayList<>();
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
		
		//add a check for consistency
		stmtList.add(genAssertConsistency(bl));
		
		for (int i = 0; i < automata.length; i++) {
			stmtList.add(genOuterIfTransition(automata[i], i, bl));
		}
		if (!stateVars.isEmpty()) {
			final List<Statement> stateVarsAssigns = genStateVarsAssign(bl);
			for (int i = 0; i < stateVarsAssigns.size(); i++) {
				stmtList.add(stateVarsAssigns.get(i));
			}
		}
		
		return stmtList.toArray(new Statement[stmtList.size()]);
	}
	
	/**
	 * Create the main loop of the pea product. This is a huge while statement that contains all transitions of all
	 * components. This procedure calls {@link genWhileBody} to create the statements of the main loop.
	 * 
	 * @param bl
	 *            Location of the procedure body.
	 * @return The while-statement.
	 */
	public Statement genWhileSmt(final BoogieLocation bl) {
		final WildcardExpression wce = new WildcardExpression(bl);
		final LoopInvariantSpecification[] invariants = new LoopInvariantSpecification[0];
		final WhileStatement whileStatement = new WhileStatement(bl, wce, invariants, genWhileBody(bl));
		return whileStatement;
	}
	
	public static Expression genPcExpr(final Phase[] phases, final Phase[] initialPhases, final int autIndex,
			final BoogieLocation bl) {
		final List<Expression> exprList = new ArrayList<>();
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
				BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier,
						intLiteral);
				if (exprList.isEmpty()) {
					exprList.add(binaryExpr);
				} else {
					binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR,
							exprList.get(exprList.size() - 1), binaryExpr);
					exprList.add(binaryExpr);
				}
			}
		}
		return exprList.get(exprList.size() - 1);
	}
	
	public Statement[] genInitialPhasesSmts(final BoogieLocation bl) {
		final VariableLHS[] ids = new VariableLHS[pcIds.size()];
		for (int i = 0; i < pcIds.size(); i++) {
			ids[i] = new VariableLHS(bl, pcIds.get(i));
		}
		final HavocStatement pcHavoc = new HavocStatement(bl, ids);
		
		final List<Expression> pcExprs = new ArrayList<>();
		for (int i = 0; i < automata.length; i++) {
			pcExprs.add(genPcExpr(automata[i].getPhases(), automata[i].getInit(), i, bl));
		}
		
		final AssumeStatement assumeSmt = new AssumeStatement(bl, genConjunction(pcExprs, bl));
		
		final Statement[] statements = new Statement[2];
		statements[0] = pcHavoc;
		statements[1] = assumeSmt;
		return statements;
	}
	
	public Expression genClockInit(final BoogieLocation bl) {
		Expression initializer = null;
		for (int i = 0; i < clockIds.size(); i++) {
			final IdentifierExpression identifier = new IdentifierExpression(bl, clockIds.get(i));
			final RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0));
			final BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier,
					realLiteral);
			if (initializer == null) {
				initializer = binaryExpr;
			} else {
				initializer = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND, initializer, binaryExpr);
			}
		}
		if (initializer == null) {
			initializer = new BooleanLiteral(bl, true);
		}
		return initializer;
	}
	
	public Statement[] genClockInitSmts(final BoogieLocation bl) {
		if (clockIds.isEmpty()) {
			return new Statement[0];
		}
		final VariableLHS[] clocks = new VariableLHS[clockIds.size()];
		int i = 0;
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
	 * One assignment is initialized (only as an example). The genWhileSmt method is called.
	 * 
	 * @param bl
	 *            Location of the procedure body.
	 * @return Statements of the procedure body which includes one assignment and one while-statement.
	 */
	public Statement[] genProcBodySmts(final BoogieLocation bl) {
		final List<Statement> statements = new ArrayList<>();
		statements.addAll(Arrays.asList(genInitialPhasesSmts(bl)));
		statements.addAll(Arrays.asList(genClockInitSmts(bl)));
		statements.add(genWhileSmt(bl));
		return statements.toArray(new Statement[statements.size()]);
	}
	
	/**
	 * The procedure statement is initialized. It is deployed to the unit. The unit is sent to the print process. The
	 * result is a Boogie text file.
	 */
	public Unit genProc() {
		final BoogieLocation bl = boogieLocations[0];
		final VariableDeclaration[] localVars = new VariableDeclaration[0];
		final Body body = new Body(bl, localVars, genProcBodySmts(bl));
		final List<String> modifiedVarsList = new ArrayList<>();
		for (int i = 0; i < clockIds.size(); i++) {
			modifiedVarsList.add(clockIds.get(i));
		}
		for (int i = 0; i < pcIds.size(); i++) {
			modifiedVarsList.add(pcIds.get(i));
		}
		modifiedVarsList.add("delta");
		
		for (int i = 0; i < stateVars.size(); i++) {
			modifiedVarsList.add(stateVars.get(i));
			modifiedVarsList.add(primedVars.get(i));
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
		final Procedure proc =
				new Procedure(bl, attribute, "myProcedure", typeParams, inParams, outParams, modArray, body);
		decList.add(proc);
		final Declaration[] decArray = decList.toArray(new Declaration[decList.size()]);
		unit.setDeclarations(decArray);
		return unit;
	}
	
	public void initBoogieLocations(final int count) {
		if (inputFilePath == null) {
			inputFilePath = boogieFilePath;
		}
		boogieLocations = new BoogieLocation[count + 1];
		boogieLocations[0] = new BoogieLocation(inputFilePath, 1, count, 0, 100, false);
		for (int i = 0; i < count; i++) {
			boogieLocations[i + 1] = new BoogieLocation(inputFilePath, i + 1, i + 1, 0, 100, false);
		}
	}
	
	public srParsePattern getRequirement(final int i) {
		return mRequirements[i];
	}
	
	public Unit genBoogie(final srParsePattern[] patterns) {
		mRequirements = patterns;
		return genBoogie(new ReqToPEA(mLogger).genPEA(patterns));
	}
	
	public Unit genBoogie(final PhaseEventAutomata[] automata) {
		initBoogieLocations(automata.length);
		
		this.automata = automata;
		genGlobVars();
		return genProc();
	}
}
