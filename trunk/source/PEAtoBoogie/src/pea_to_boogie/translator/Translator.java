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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
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
	public List<Declaration> decList = new ArrayList<Declaration>();
	/**
	 * The list of clock identifiers.
	 */
	public List<String> clockIds = new ArrayList<String>();
	/**
	 * The list of unique identifiers. Each identifier is in the form of "pc" + phaseIndex. Each automaton has an array
	 * of phases. The location of each phase in that array specifies the value of phaseIndex.
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

	/**
	 * Set the input file name. This is used to annotate the Boogie code with the right file name. The Location object
	 * should contain the name of the original file name.
	 * 
	 * @param The
	 *            input file name.
	 */
	public void setInputFilePath(String path) {
		this.inputFilePath = path;
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
	 * Add a bitset containing the numbers of the components for which vacuity should be checked.
	 * 
	 * @param vacuityChecks
	 *            the bitset. Bit i is set if we should check vacuity for the i-th property.
	 */
	public void setVacuityChecks(BitSet vacuityChecks) {
		this.mVacuityChecks = vacuityChecks;
	}

	public boolean checkVacuity(int propertyNum) {
		return mVacuityChecks != null && mVacuityChecks.get(propertyNum);
	}

	/**
	 * Assign a value to the combinationNum.
	 * 
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
			BoogieLocation blUnit = boogieLocations[0];
			BoogieLocation blVar = blUnit;
			BoogieLocation blPrimType = blUnit;

			for (int i = 0; i < this.automata.length; i++) {
				List<String> tempClocks = this.automata[i].getClocks();
				for (int j = 0; j < tempClocks.size(); j++) {
					this.clockIds.add(tempClocks.get(j));
				}
			}
			ASTType astType = new PrimitiveType(blPrimType, "real");
			VarList clockVars = new VarList(blVar, this.clockIds.toArray(new String[this.clockIds.size()]), astType);

			List<String> extraVars = new ArrayList<String>();
			for (int i = 0; i < this.automata.length; i++) {
				this.pcIds.add("pc" + i);
				extraVars.add("pc" + i);
			}
			astType = new PrimitiveType(blPrimType, "int");
			VarList pcVar = new VarList(blVar, extraVars.toArray(new String[extraVars.size()]), astType);

			boolean visited = false;
			for (int i = 0; i < this.automata.length; i++) {
				// System.out.println(this.automata[i].getVariables().size());

				Map<String, String> map = this.automata[i].getVariables();

				for (String name : map.keySet()) {
					if (map.get(name).equals("boolean")) {
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
			VarList deltaVar = new VarList(blVar, extraVars.toArray(new String[extraVars.size()]), astType);
			List<VarList> varList = new ArrayList<VarList>();
			if (!this.clockIds.isEmpty())
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
				VarList stVars = new VarList(blVar, stVarsList.toArray(new String[stVarsList.size()]), astType);
				varList.add(stVars);
			}

			if (this.eventVars.size() != 0) {
				astType = new PrimitiveType(blPrimType, "bool");
				VarList evVars = new VarList(blVar, this.eventVars.toArray(new String[this.eventVars.size()]), astType);
				varList.add(evVars);
			}
			Attribute[] attribute = new Attribute[0];
			VariableDeclaration vars = new VariableDeclaration(blVar, attribute,
					varList.toArray(new VarList[varList.size()]));
			this.decList.add(vars);
			Declaration[] decArray = this.decList.toArray(new Declaration[this.decList.size()]);
			this.unit = new Unit(blUnit, decArray);
		} catch (Exception e) {
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
	public Expression genConjunction(List<Expression> exprs, BoogieLocation bl) {
		Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext())
			return new BooleanLiteral(bl, true);
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
	public Expression genDisjunction(List<Expression> exprs, BoogieLocation bl) {
		Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext())
			return new BooleanLiteral(bl, false);
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
	public Statement genClockPlusDelta(String clockId, BoogieLocation bl) {
		VariableLHS clockVar = new VariableLHS(bl, clockId);

		IdentifierExpression clockID = new IdentifierExpression(bl, clockId);
		IdentifierExpression deltaID = new IdentifierExpression(bl, "delta");
		BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.ARITHPLUS, clockID, deltaID);
		LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = clockVar;
		Expression[] expr = new Expression[1];
		expr[0] = binaryExpr;
		AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);

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
	public Statement[] genDelay(BoogieLocation bl) {

		List<VariableLHS> havocIds = new ArrayList<VariableLHS>();
		for (int i = 0; i < this.primedVars.size(); i++) {
			havocIds.add(new VariableLHS(bl, this.primedVars.get(i)));
		}
		for (int i = 0; i < this.eventVars.size(); i++) {
			havocIds.add(new VariableLHS(bl, this.eventVars.get(i)));
		}
		havocIds.add(new VariableLHS(bl, "delta"));
		VariableLHS[] ids = havocIds.toArray(new VariableLHS[havocIds.size()]);
		HavocStatement havocSmt = new HavocStatement(bl, ids);
		IdentifierExpression identifier = new IdentifierExpression(bl, "delta");
		RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0.0));
		BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPGT, identifier,
				realLiteral);
		AssumeStatement assumeDelta = new AssumeStatement(bl, binaryExpr);

		Statement[] smtArray = new Statement[this.clockIds.size()];
		for (int i = 0; i < this.clockIds.size(); i++) {
			smtArray[i] = genClockPlusDelta(this.clockIds.get(i), bl);
		}
		Statement[] statements = new Statement[smtArray.length + 2];
		statements[0] = havocSmt;
		statements[1] = assumeDelta;
		for (int i = 2; i < statements.length; i++) {

			statements[i] = smtArray[i - 2];
		}
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
	public Expression genComparePhaseCounter(int phaseIndex, int autIndex, BoogieLocation bl) {
		IdentifierExpression identifier = new IdentifierExpression(bl, "pc" + autIndex);
		IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(phaseIndex));
		BinaryExpression ifCon = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier, intLiteral);
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
	public Statement[] genCheckPhaseInvariant(Phase phase, BoogieLocation bl) {
		Expression expr = new CDDTranslator().CDD_To_Boogie(phase.getClockInvariant(), getBoogieFilePath(), bl);
		AssumeStatement assumeClInv = new AssumeStatement(bl, expr);
		expr = new CDDTranslator().CDD_To_Boogie(phase.getStateInvariant(), getBoogieFilePath(), bl);
		AssumeStatement assumeStateInv = new AssumeStatement(bl, expr);
		Statement[] statements = new Statement[2];
		statements[0] = assumeClInv;
		statements[1] = assumeStateInv;
		return statements;
	}

	public Statement joinIfSmts(Statement[] statements, BoogieLocation bl) {

		List<Statement> smtList = new ArrayList<Statement>();
		for (int i = 0; i < statements.length; i++) {
			IfStatement oldIfSmt = (IfStatement) statements[i];
			if (smtList.size() == 0) {
				Statement[] emptyArray = new Statement[0];
				IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), emptyArray);
				smtList.add(newIfSmt);
			} else {
				Statement[] smt = new Statement[1];
				smt[0] = smtList.get(smtList.size() - 1);
				IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
				smtList.add(newIfSmt);
			}
		}

		return smtList.get(smtList.size() - 1);
	}

	public Statement joinInnerIfSmts(Statement[] statements, BoogieLocation bl) {

		List<Statement> smtList = new ArrayList<Statement>();
		for (int i = 0; i < statements.length; i++) {
			IfStatement oldIfSmt = (IfStatement) statements[i];
			if (smtList.size() == 0) {
				BooleanLiteral bLiteral = new BooleanLiteral(bl, false);
				AssumeStatement assumeFalse = new AssumeStatement(bl, bLiteral);
				Statement[] smt = new Statement[1];
				smt[0] = assumeFalse;
				IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
				smtList.add(newIfSmt);
			} else {
				Statement[] smt = new Statement[1];
				smt[0] = smtList.get(smtList.size() - 1);
				IfStatement newIfSmt = new IfStatement(bl, oldIfSmt.getCondition(), oldIfSmt.getThenPart(), smt);
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
	public Statement genCheckInvariants(PhaseEventAutomata automaton, int autIndex, BoogieLocation bl) {

		Phase[] phases = automaton.getPhases();
		Statement[] statements = new Statement[phases.length];
		for (int i = 0; i < phases.length; i++) {
			Expression ifCon = genComparePhaseCounter(i, autIndex, bl);
			Statement[] emptyArray = new Statement[0];
			IfStatement ifStatement = new IfStatement(bl, ifCon, genCheckPhaseInvariant(phases[i], bl), emptyArray);
			statements[i] = ifStatement;
		}
		Statement statement = joinIfSmts(statements, bl);
		return statement;
	}

	public Statement genReset(String resetVar, BoogieLocation bl) {
		VariableLHS reset = new VariableLHS(bl, resetVar);

		RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0.0));
		LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = reset;
		Expression[] expr = new Expression[1];
		expr[0] = realLiteral;
		AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);

		return assignment;
	}

	public Statement genPCAssign(int autIndex, int phaseIndex, BoogieLocation bl) {
		VariableLHS pc = new VariableLHS(bl, "pc" + autIndex);

		IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(phaseIndex));
		LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = pc;
		Expression[] expr = new Expression[1];
		expr[0] = intLiteral;
		AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);

		return assignment;
	}

	public Statement[] genInnerIfBody(PhaseEventAutomata automaton, Transition transition, int autIndex,
			BoogieLocation bl) {

		List<Statement> smtList = new ArrayList<Statement>();
		// StringLiteral strLiteral = new StringLiteral(blAssumeGuard,
		// CDDTranslation.CDD_To_Boogie(transition.getGuard()));
		Expression expr = new CDDTranslator().CDD_To_Boogie(transition.getGuard(), getBoogieFilePath(), bl);
		AssumeStatement assumeGuard = new AssumeStatement(bl, expr);
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
			if (phases[i].getName().equals(desPhase.getName()))
				phaseIndex = i;
		}
		smtList.add(genPCAssign(autIndex, phaseIndex, bl));

		Statement[] statements = smtList.toArray(new Statement[smtList.size()]);
		return statements;
	}

	public Statement genOuterIfBody(PhaseEventAutomata automaton, Phase phase, int autIndex, BoogieLocation bl) {

		Statement[] statements = new Statement[phase.getTransitions().size()];
		List<Transition> transitions = phase.getTransitions();
		for (int i = 0; i < transitions.size(); i++) {
			WildcardExpression wce = new WildcardExpression(bl);
			Statement[] emptyArray = new Statement[0];
			IfStatement ifStatement = new IfStatement(bl, wce,
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
			Expression ifCon = genComparePhaseCounter(i, autIndex, bl);
			Statement[] emptyArray = new Statement[0];
			Statement[] outerIfBodySmt = new Statement[1];
			outerIfBodySmt[0] = genOuterIfBody(automaton, phases[i], autIndex, bl);
			IfStatement ifStatement = new IfStatement(bl, ifCon, outerIfBodySmt, emptyArray);
			statements[i] = ifStatement;
		}
		Statement statement = joinIfSmts(statements, bl);

		return statement;
	}

	public List<Statement> genStateVarsAssign(BoogieLocation bl) {
		List<Statement> statements = new ArrayList<Statement>();
		for (int i = 0; i < this.stateVars.size(); i++) {
			VariableLHS lhsVar = new VariableLHS(bl, this.stateVars.get(i));
			IdentifierExpression rhs = new IdentifierExpression(bl, this.primedVars.get(i));
			LeftHandSide[] lhs = new LeftHandSide[1];
			lhs[0] = lhsVar;
			Expression[] expr = new Expression[1];
			expr[0] = rhs;
			AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
			statements.add(assignment);
		}
		return statements;
	}

	public Statement genAssertRTInconsistency(int[] permutation, BoogieLocation bl) {
		ConditionGenerator conGen = new ConditionGenerator();
		conGen.setTranslator(this);
		Expression expr = conGen.nonDLCGenerator(this.automata, permutation, getBoogieFilePath(), bl);
		if (expr == null)
			return null;
		ReqCheck check = new ReqCheck(ReqCheck.ReqSpec.RTINCONSISTENT, permutation, this);
		ReqLocation loc = new ReqLocation(check);
		AssertStatement assertSmt = new AssertStatement(loc, expr);
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
	private Statement genAssertNonVacuous(PhaseEventAutomata pea, int automatonIndex, BoogieLocation bl) {
		Phase[] phases = pea.getPhases();

		// compute the maximal phase number occurring in the automaton.
		int maxBits = 0;
		for (Phase phase : phases) {
			PhaseBits bits = phase.getPhaseBits();
			// ignore start node when computing max phase
			if (bits != null) {
				int act = bits.getActive();
				if (act > maxBits) {
					maxBits = act;
				}
			}
		}
		int pnr = 0;
		while ((1 << pnr) <= maxBits)
			pnr++;

		// check that one of those phases is eventually reached.
		List<Expression> checkReached = new ArrayList<Expression>();
		for (int i = 0; i < phases.length; i++) {
			PhaseBits bits = phases[i].getPhaseBits();
			if (bits == null || (bits.getActive() & (1 << (pnr - 1))) == 0)
				checkReached.add(genComparePhaseCounter(i, automatonIndex, bl));
		}
		if (checkReached.isEmpty())
			return null;
		Expression disjunction = genDisjunction(checkReached, bl);
		ReqCheck check = new ReqCheck(ReqCheck.ReqSpec.VACUOUS, new int[] { automatonIndex }, this);
		ReqLocation loc = new ReqLocation(check);
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
		final List<Statement> stmtList = new ArrayList<Statement>();
		stmtList.addAll(Arrays.asList(genDelay(bl)));

		for (int i = 0; i < this.automata.length; i++) {
			stmtList.add(genCheckInvariants(this.automata[i], i, bl));
		}
		int[] automataIndices = new int[automata.length];
		for (int i = 0; i < this.automata.length; i++) {
			automataIndices[i] = i;
		}
		for (int[] subset : new Permutation().subArrays(automataIndices, this.combinationNum)) {
			Statement assertStmt = genAssertRTInconsistency(subset, bl);
			if (assertStmt != null)
				stmtList.add(assertStmt);
		}
		for (int i = 0; i < this.automata.length; i++) {
			if (checkVacuity(i)) {
				Statement assertStmt = genAssertNonVacuous(this.automata[i], i, bl);
				if (assertStmt != null)
					stmtList.add(assertStmt);
			}
		}
		
		//add a check for consistency
		stmtList.add(genAssertConsistency(bl));

		for (int i = 0; i < this.automata.length; i++) {
			stmtList.add(genOuterIfTransition(this.automata[i], i, bl));
		}
		if (this.stateVars.size() != 0) {
			List<Statement> stateVarsAssigns = genStateVarsAssign(bl);
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
	public Statement genWhileSmt(BoogieLocation bl) {
		WildcardExpression wce = new WildcardExpression(bl);
		LoopInvariantSpecification[] invariants = new LoopInvariantSpecification[0];
		WhileStatement whileStatement = new WhileStatement(bl, wce, invariants, genWhileBody(bl));
		return whileStatement;
	}

	public Expression genPcExpr(Phase[] phases, Phase[] initialPhases, int autIndex, BoogieLocation bl) {
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
				IdentifierExpression identifier = new IdentifierExpression(bl, "pc" + autIndex);
				IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(i));
				BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier,
						intLiteral);
				if (exprList.size() == 0) {
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

	public Statement[] genInitialPhasesSmts(BoogieLocation bl) {
		VariableLHS[] ids = new VariableLHS[this.pcIds.size()];
		for (int i = 0; i < this.pcIds.size(); i++) {
			ids[i] = new VariableLHS(bl, this.pcIds.get(i));
		}
		HavocStatement pcHavoc = new HavocStatement(bl, ids);

		List<Expression> pcExprs = new ArrayList<Expression>();
		for (int i = 0; i < this.automata.length; i++) {
			pcExprs.add(genPcExpr(this.automata[i].getPhases(), this.automata[i].getInit(), i, bl));
		}

		AssumeStatement assumeSmt = new AssumeStatement(bl, genConjunction(pcExprs, bl));

		Statement[] statements = new Statement[2];
		statements[0] = pcHavoc;
		statements[1] = assumeSmt;
		return statements;
	}

	public Expression genClockInit(BoogieLocation bl) {
		Expression initializer = null;
		for (int i = 0; i < this.clockIds.size(); i++) {
			IdentifierExpression identifier = new IdentifierExpression(bl, this.clockIds.get(i));
			RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0));
			BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier,
					realLiteral);
			if (initializer == null) {
				initializer = binaryExpr;
			} else {
				initializer = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND, initializer, binaryExpr);
			}
		}
		if (initializer == null)
			initializer = new BooleanLiteral(bl, true);
		return initializer;
	}

	public Statement[] genClockInitSmts(BoogieLocation bl) {
		if (clockIds.isEmpty()) {
			return new Statement[0];
		}
		VariableLHS[] clocks = new VariableLHS[clockIds.size()];
		int i = 0;
		for (String clkId : this.clockIds)
			clocks[i++] = new VariableLHS(bl, clkId);
		HavocStatement clockHavoc = new HavocStatement(bl, clocks);
		AssumeStatement assumeSmt = new AssumeStatement(bl, genClockInit(bl));

		Statement[] statements = new Statement[2];
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
	public Statement[] genProcBodySmts(BoogieLocation bl) {
		List<Statement> statements = new ArrayList<Statement>();
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
		BoogieLocation bl = boogieLocations[0];
		VariableDeclaration[] localVars = new VariableDeclaration[0];
		Body body = new Body(bl, localVars, genProcBodySmts(bl));
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
		VariableLHS[] modifiedVars = new VariableLHS[modifiedVarsList.size()];
		for (int i = 0; i < modifiedVars.length; i++) {
			modifiedVars[i] = new VariableLHS(bl, modifiedVarsList.get(i));
		}
		ModifiesSpecification mod = new ModifiesSpecification(bl, false, modifiedVars);
		ModifiesSpecification[] modArray = new ModifiesSpecification[1];
		modArray[0] = mod;
		Attribute[] attribute = new Attribute[0];
		String[] typeParams = new String[0];
		VarList[] inParams = new VarList[0];
		VarList[] outParams = new VarList[0];
		Procedure proc = new Procedure(bl, attribute, "myProcedure", typeParams, inParams, outParams, modArray, body);
		decList.add(proc);
		Declaration[] decArray = decList.toArray(new Declaration[decList.size()]);
		unit.setDeclarations(decArray);
		return unit;
	}

	public void initBoogieLocations(int count) {
		if (inputFilePath == null)
			inputFilePath = boogieFilePath;
		boogieLocations = new BoogieLocation[count + 1];
		boogieLocations[0] = new BoogieLocation(inputFilePath, 1, count, 0, 100, false);
		for (int i = 0; i < count; i++) {
			boogieLocations[i + 1] = new BoogieLocation(inputFilePath, i + 1, i + 1, 0, 100, false);
		}
	}

	public srParsePattern getRequirement(int i) {
		return mRequirements[i];
	}

	public Unit genBoogie(srParsePattern[] patterns) {
		this.mRequirements = patterns;
		return genBoogie(new ReqToPEA().genPEA(patterns));
	}

	public Unit genBoogie(PhaseEventAutomata[] automata) {
		initBoogieLocations(automata.length);

		this.automata = automata;
		genGlobVars();
		return genProc();
	}
}
