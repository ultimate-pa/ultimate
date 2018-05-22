/*
 * Copyright (C) 2013-2017 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
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
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseBits;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.ConditionGenerator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.ReqToPEA;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

/**
 * This class translates a phase event automaton to an equivalent Boogie code.
 *
 * @author Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class Req2BoogieTranslator {

	private static final Attribute[] EMPTY_ATTRIBUTES = new Attribute[0];

	private final Unit mUnit;
	private final List<String> mClockIds;
	private final List<String> mPcIds;
	private final Map<String, ASTType> mStateVars;
	private final Map<String, ASTType> mConstVars;
	private final Map<String, ASTType> mPrimedVars;
	private final Map<String, ASTType> mEventVars;
	private final Map<PatternType, PhaseEventAutomata> mReq2Automata;
	private final Map<PatternType, BoogieLocation> mReq2Loc;
	private final BoogieLocation mUnitLocation;

	private final boolean mCheckVacuity;
	private final int mCombinationNum;
	private final boolean mCheckConsistency;
	private final boolean mReportTrivialConsistency;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final NormalFormTransformer<Expression> mNormalFormTransformer;

	private final PeaResultUtil mPeaResultUtil;

	public Req2BoogieTranslator(final IUltimateServiceProvider services, final ILogger logger,
			final boolean vacuityCheck, final int num, final boolean checkConsistency,
			final boolean reportTrivialRtConsistency, final List<PatternType> patterns) {
		mLogger = logger;
		mServices = services;
		mCheckVacuity = vacuityCheck;
		mReportTrivialConsistency = reportTrivialRtConsistency;
		mCombinationNum = num;
		mCheckConsistency = checkConsistency;

		mPeaResultUtil = new PeaResultUtil(mLogger, mServices);

		mClockIds = new ArrayList<>();
		mPcIds = new ArrayList<>();
		mStateVars = new LinkedHashMap<>();
		mConstVars = new LinkedHashMap<>();
		mPrimedVars = new LinkedHashMap<>();
		mEventVars = new LinkedHashMap<>();
		mNormalFormTransformer = new NormalFormTransformer<>(new BoogieExpressionTransformer());

		final List<InitializationPattern> init = patterns.stream().filter(a -> a instanceof InitializationPattern)
				.map(a -> (InitializationPattern) a).collect(Collectors.toList());
		final List<PatternType> requirements =
				patterns.stream().filter(a -> !(a instanceof InitializationPattern)).collect(Collectors.toList());
		final Map<String, Integer> id2bounds = genId2Bounds(init);

		mReq2Automata = new ReqToPEA(mServices, mLogger).genPEA(requirements, id2bounds);
		// TODO: initBoogieLocations is completely broken. Rewrite.
		mReq2Loc = generateBoogieLocations(patterns);
		mUnitLocation = generateUnitLocation(patterns);
		final List<Declaration> decls = new ArrayList<>();
		decls.addAll(generateGlobalVars(init));
		decls.add(generateProcedures(init));

		mUnit = new Unit(mUnitLocation, decls.toArray(new Declaration[decls.size()]));
	}

	private static BoogieLocation generateUnitLocation(final List<PatternType> patterns) {
		// TODO: Add locations to pattern type to generate meaningful boogie locations
		return new BoogieLocation("", -1, -1, -1, -1);
	}

	private static Map<PatternType, BoogieLocation> generateBoogieLocations(final List<PatternType> patterns) {
		// TODO: Add locations to pattern type to generate meaningful boogie locations
		final Map<PatternType, BoogieLocation> rtr = new HashMap<>();
		for (final PatternType pattern : patterns) {
			rtr.put(pattern, new BoogieLocation("", -1, -1, -1, -1));
		}
		return rtr;
	}

	public Unit getUnit() {
		return mUnit;
	}

	private Map<String, Integer> genId2Bounds(final List<InitializationPattern> inits) {
		final Map<String, Integer> rtr = new HashMap<>();
		final Predicate<InitializationPattern> pred = a -> {
			final BoogiePrimitiveType type = toPrimitiveTypeNoError(a.getType());
			return type == BoogieType.TYPE_INT || type == BoogieType.TYPE_REAL;
		};
		final Iterator<InitializationPattern> iter =
				inits.stream().filter(a -> a.getCategory() == VariableCategory.CONST).filter(pred).iterator();
		while (iter.hasNext()) {
			final InitializationPattern init = iter.next();
			final Expression expr = init.getExpression();
			final Integer val;
			if (expr instanceof RealLiteral) {
				val = tryParseInt(init, ((RealLiteral) expr).getValue());
			} else if (expr instanceof IntegerLiteral) {
				val = tryParseInt(init, ((IntegerLiteral) expr).getValue());
			} else {
				val = null;
				mPeaResultUtil.syntaxError(mReq2Loc.get(init),
						"Cannot convert CONST with expression " + BoogiePrettyPrinter.print(expr) + " to duration");
			}
			if (val == null) {
				continue;
			}
			rtr.put(init.getId(), val);
		}
		return rtr;
	}

	private Integer tryParseInt(final PatternType pattern, final String val) {
		try {
			return new BigDecimal(val).toBigIntegerExact().intValueExact();
		} catch (NumberFormatException | ArithmeticException ex) {
			mPeaResultUtil.syntaxError(mReq2Loc.get(pattern),
					"Cannot convert CONST with value " + val + " to duration (must be integer)");
			return null;
		}

	}

	private Set<String> getPrimedVars() {
		return Collections.unmodifiableSet(mPrimedVars.keySet());
	}

	private BoogiePrimitiveType toPrimitiveType(final String type, final ILocation loc) {
		final BoogiePrimitiveType rtr = toPrimitiveTypeNoError(type);
		if (rtr == BoogieType.TYPE_ERROR) {
			mPeaResultUtil.syntaxError(loc, "Unknown type " + type);
		}
		return rtr;
	}

	private static BoogiePrimitiveType toPrimitiveTypeNoError(final String type) {
		switch (type.toLowerCase()) {
		case "bool":
			return BoogieType.TYPE_BOOL;
		case "real":
			return BoogieType.TYPE_REAL;
		case "int":
			return BoogieType.TYPE_INT;
		default:
			return BoogieType.TYPE_ERROR;
		}
	}

	private List<Declaration> generateGlobalVars(final List<InitializationPattern> inits) {
		final PrimitiveType realType = new PrimitiveType(mUnitLocation, "real");
		final PrimitiveType intType = new PrimitiveType(mUnitLocation, "int");
		final List<VarList> varLists = new ArrayList<>();

		// declare delta var
		varLists.add(new VarList(mUnitLocation, new String[] { "delta" }, realType));

		// extract state vars from init pattern
		for (final InitializationPattern init : inits) {
			final ILocation loc = mReq2Loc.get(init);
			final ASTType type = toPrimitiveType(init.getType(), loc).toASTType(loc);
			final String name = init.getId();
			if (type.getBoogieType() == BoogieType.TYPE_ERROR) {
				mLogger.error(name + " has type None");
			}
			if (init.getCategory() != VariableCategory.CONST) {
				addStateVar(name, type, loc);
			} else {
				addConstVar(name, type, loc);
			}

		}

		// extract pcid vars, clock vars, state vars, primed state vars, and event vars
		extractVariablesFromAutomata();

		if (!mClockIds.isEmpty()) {
			varLists.add(new VarList(mUnitLocation, mClockIds.toArray(new String[mClockIds.size()]), realType));
		}

		if (!mPcIds.isEmpty()) {
			varLists.add(new VarList(mUnitLocation, mPcIds.toArray(new String[mPcIds.size()]), intType));
		}

		varLists.addAll(createVarLists(mConstVars));
		varLists.addAll(createVarLists(mStateVars));
		varLists.addAll(createVarLists(mPrimedVars));
		varLists.addAll(createVarLists(mEventVars));

		final List<Declaration> vardecls = new ArrayList<>();
		for (final VarList varlist : varLists) {
			final VariableDeclaration varDecl =
					new VariableDeclaration(mUnitLocation, EMPTY_ATTRIBUTES, new VarList[] { varlist });
			vardecls.add(varDecl);
		}
		return vardecls;
	}

	private static Collection<? extends VarList> createVarLists(final Map<String, ASTType> varMap) {
		if (varMap.isEmpty()) {
			return Collections.emptyList();
		}

		final Collection<VarList> rtr = new ArrayList<>();
		for (final Entry<String, ASTType> entry : varMap.entrySet()) {
			rtr.add(new VarList(entry.getValue().getLoc(), new String[] { entry.getKey() }, entry.getValue()));
		}
		return rtr;
	}

	private void extractVariablesFromAutomata() {
		for (final Entry<PatternType, PhaseEventAutomata> pattern2Aut : mReq2Automata.entrySet()) {
			final PhaseEventAutomata currentAutomaton = pattern2Aut.getValue();
			final BoogieLocation loc = mReq2Loc.get(pattern2Aut.getKey());
			mPcIds.add(getPcName(currentAutomaton));
			mClockIds.addAll(currentAutomaton.getClocks());
			final Map<String, String> varMap = currentAutomaton.getVariables();

			for (final Entry<String, String> entry : varMap.entrySet()) {
				final String name = entry.getKey();
				final String type = entry.getValue();

				if (type == null) {
					checkVarDeclared(loc, currentAutomaton, name);
					continue;
				}

				switch (type.toLowerCase()) {
				case "bool":
				case "real":
				case "int":
					checkVarDeclared(loc, currentAutomaton, name);
					break;
				case "event":
					mEventVars.put(name, getBoogieType("bool", loc));
					break;
				default:
					mLogger.warn("Skipping unknown PEA variable type " + type);
				}
			}
		}
	}

	private void checkVarDeclared(final ILocation loc, final PhaseEventAutomata currentAutomaton, final String name) {
		if (!mStateVars.containsKey(name) && !mConstVars.containsKey(name)) {
			mPeaResultUtil.syntaxError(loc, "Variable " + name + " not declared in " + currentAutomaton.getName());
		}
	}

	private void addStateVar(final String name, final ASTType astType, final ILocation loc) {
		final ASTType oldType = mStateVars.put(name, astType);
		if (oldType == null) {
			mPrimedVars.put(getPrimedVar(name), astType);
		}

		checkMultipleDecls(name, astType, loc, oldType);
	}

	private void addConstVar(final String name, final ASTType astType, final ILocation loc) {
		final ASTType oldType = mConstVars.put(name, astType);
		if (oldType == null) {
			mPrimedVars.put(getPrimedVar(name), astType);
		}
		checkMultipleDecls(name, astType, loc, oldType);
	}

	private void checkMultipleDecls(final String name, final ASTType astType, final ILocation loc,
			final ASTType oldType) {
		if (oldType != null && astType != null && !Objects.equals(oldType.getBoogieType(), astType.getBoogieType())) {
			mPeaResultUtil.syntaxError(loc, "Variable declared multiple times with different type: " + name + " : "
					+ oldType.getBoogieType() + " vs. " + astType.getBoogieType());
		}
	}

	private ASTType getBoogieType(final String value, final ILocation loc) {
		return toPrimitiveType(value, loc).toASTType(loc);
	}

	private static String getPrimedVar(final String name) {
		return name + "'";
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
	private Expression genDisjunction(final List<Expression> exprs, final BoogieLocation bl) {
		final Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext()) {
			return ExpressionFactory.createBooleanLiteral(bl, false);
		}
		Expression cnf = it.next();
		while (it.hasNext()) {
			cnf = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.LOGICOR, cnf, it.next());
		}
		return mNormalFormTransformer.toNnf(cnf);
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
	private static Statement genClockPlusDelta(final String clockId, final BoogieLocation bl) {
		final VariableLHS clockVar = new VariableLHS(bl, clockId);

		final IdentifierExpression clockID = new IdentifierExpression(bl, clockId);
		final IdentifierExpression deltaID = new IdentifierExpression(bl, "delta");
		final BinaryExpression binaryExpr =
				new BinaryExpression(bl, BinaryExpression.Operator.ARITHPLUS, clockID, deltaID);
		final LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = clockVar;
		final Expression[] expr = new Expression[1];
		expr[0] = binaryExpr;
		return new AssignmentStatement(bl, lhs, expr);
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
	private Statement[] genDelay(final BoogieLocation bl) {

		final List<VariableLHS> havocIds = new ArrayList<>();
		for (final String primedVar : mPrimedVars.keySet()) {
			havocIds.add(new VariableLHS(bl, primedVar));
		}
		for (final String eventVar : mEventVars.keySet()) {
			havocIds.add(new VariableLHS(bl, eventVar));
		}
		havocIds.add(new VariableLHS(bl, "delta"));
		final VariableLHS[] ids = havocIds.toArray(new VariableLHS[havocIds.size()]);
		final HavocStatement havocSmt = new HavocStatement(bl, ids);
		final IdentifierExpression identifier = new IdentifierExpression(bl, "delta");
		final RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0.0));
		final BinaryExpression binaryExpr =
				new BinaryExpression(bl, BinaryExpression.Operator.COMPGT, identifier, realLiteral);
		final AssumeStatement assumeDelta = new AssumeStatement(bl, binaryExpr);

		final Statement[] smtArray = new Statement[mClockIds.size()];
		for (int i = 0; i < mClockIds.size(); i++) {
			smtArray[i] = genClockPlusDelta(mClockIds.get(i), bl);
		}
		final Statement[] statements = new Statement[smtArray.length + 2];
		statements[0] = havocSmt;
		statements[1] = assumeDelta;
		System.arraycopy(smtArray, 0, statements, 2, smtArray.length);
		return statements;
	}

	/**
	 * Generate the expression <code><i>pcName</i> == <i>phaseIndex</i></code> that checks if the automaton with a pc
	 * named pcName is currently in the phase phaseIndex.
	 *
	 * @param phaseIndex
	 *            the index of the phase we check for.
	 * @param pcName
	 *            the name of the pc variable for this automaton
	 * @param bl
	 * @return
	 */
	private static Expression genComparePhaseCounter(final int phaseIndex, final String pcName,
			final BoogieLocation bl) {
		final IdentifierExpression identifier = ExpressionFactory.constructIdentifierExpression(bl, BoogieType.TYPE_INT,
				pcName, DeclarationInformation.DECLARATIONINFO_GLOBAL);
		final IntegerLiteral intLiteral = ExpressionFactory.createIntegerLiteral(bl, Integer.toString(phaseIndex));
		return ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier, intLiteral);
	}

	public static String getPcName(final PhaseEventAutomata aut) {
		return aut.getName() + "_pc";
	}

	/**
	 * Creates the code that checks the phase invariant of the given phase.
	 *
	 * @param phase
	 *            the phase whose invariant should be checked.
	 * @param bl
	 * @return the array of (two) statements that check the invariant.
	 */
	private Statement[] genCheckPhaseInvariant(final Phase phase, final BoogieLocation bl) {
		final CDD clockInvCdd = phase.getClockInvariant();
		final AssumeStatement assumeClInv;
		if (clockInvCdd != CDD.TRUE) {
			final Expression clInv = new CDDTranslator().toBoogie(clockInvCdd, bl);
			assumeClInv = new AssumeStatement(bl, mNormalFormTransformer.toNnf(clInv));
		} else {
			assumeClInv = null;
		}
		final CDD stateInvCdd = phase.getStateInvariant();
		final AssumeStatement assumeStateInv;
		if (stateInvCdd != CDD.TRUE) {
			final Expression stateInv = new CDDTranslator().toBoogie(stateInvCdd, bl);
			assumeStateInv = new AssumeStatement(bl, mNormalFormTransformer.toNnf(stateInv));
		} else {
			assumeStateInv = null;
		}
		return concatStmt(assumeClInv, assumeStateInv);
	}

	private static Statement[] concatStmt(final Statement... stmts) {
		if (stmts == null || stmts.length == 0) {
			throw new IllegalArgumentException();
		}
		final List<Statement> stmtList = Arrays.stream(stmts).filter(a -> a != null).collect(Collectors.toList());
		if (stmtList.isEmpty()) {
			throw new IllegalArgumentException();
		}
		return stmtList.toArray(new Statement[stmtList.size()]);
	}

	private static Statement joinIfSmts(final Statement[] statements, final BoogieLocation bl) {
		IfStatement acc = null;
		for (int i = 0; i < statements.length; i++) {
			final IfStatement currentIfSmt = (IfStatement) statements[i];
			assert currentIfSmt.getElsePart().length == 0;
			if (acc == null) {
				acc = currentIfSmt;
			} else {
				acc = new IfStatement(bl, currentIfSmt.getCondition(), currentIfSmt.getThenPart(),
						new Statement[] { acc });
			}
		}
		return acc;
	}

	private static Statement joinInnerIfSmts(final Statement[] statements, final BoogieLocation bl) {

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
	 * @param bl
	 *            The location information to correspond the generated source to the property.
	 * @return The if statement checking the p
	 */
	private List<Statement> genInvariantGuards(final PhaseEventAutomata automaton, final String pcName,
			final BoogieLocation bl) {
		final Phase[] phases = automaton.getPhases();
		assert phases.length > 0;
		// TODO: Keep the if in this case; may be helpful for vacuity reason extraction
		// if (phases.length == 1) {
		// return Arrays.asList(genCheckPhaseInvariant(phases[0], bl));
		// }

		final Statement[] statements = new Statement[phases.length];
		final Statement[] emptyArray = new Statement[0];
		for (int i = 0; i < phases.length; i++) {
			final Expression ifCon = genComparePhaseCounter(i, pcName, bl);
			statements[i] = new IfStatement(bl, ifCon, genCheckPhaseInvariant(phases[i], bl), emptyArray);
		}
		return Collections.singletonList(joinIfSmts(statements, bl));
	}

	private static Statement genReset(final String resetVar, final BoogieLocation bl) {
		final VariableLHS reset = new VariableLHS(bl, resetVar);

		final RealLiteral realLiteral = new RealLiteral(bl, Double.toString(0.0));
		final LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = reset;
		final Expression[] expr = new Expression[1];
		expr[0] = realLiteral;
		final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);

		return assignment;
	}

	private static Statement genPCAssign(final String pcName, final int phaseIndex, final BoogieLocation bl) {
		final VariableLHS pc = new VariableLHS(bl, pcName);

		final IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(phaseIndex));
		final LeftHandSide[] lhs = new LeftHandSide[1];
		lhs[0] = pc;
		final Expression[] expr = new Expression[1];
		expr[0] = intLiteral;
		final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);

		return assignment;
	}

	private Statement[] genInnerIfBody(final PhaseEventAutomata automaton, final String pcName,
			final Transition transition, final BoogieLocation bl) {

		final List<Statement> smtList = new ArrayList<>();
		final CDD guardCdd = transition.getGuard();
		if (guardCdd != CDD.TRUE) {
			final Expression expr = new CDDTranslator().toBoogie(guardCdd, bl);
			final AssumeStatement assumeGuard = new AssumeStatement(bl, mNormalFormTransformer.toNnf(expr));
			smtList.add(assumeGuard);
		}

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
		smtList.add(genPCAssign(pcName, phaseIndex, bl));

		return smtList.toArray(new Statement[smtList.size()]);
	}

	private Statement genOuterIfBody(final PhaseEventAutomata automaton, final String pcName, final Phase phase,
			final BoogieLocation bl) {

		final Statement[] statements = new Statement[phase.getTransitions().size()];
		final Statement[] emptyArray = new Statement[0];
		final WildcardExpression wce = new WildcardExpression(bl);
		final List<Transition> transitions = phase.getTransitions();
		for (int i = 0; i < transitions.size(); i++) {
			statements[i] =
					new IfStatement(bl, wce, genInnerIfBody(automaton, pcName, transitions.get(i), bl), emptyArray);
		}
		return joinInnerIfSmts(statements, bl);
	}

	private Statement genOuterIfTransition(final PhaseEventAutomata automaton, final String pcName,
			final BoogieLocation bl) {
		final Phase[] phases = automaton.getPhases();
		final Statement[] statements = new Statement[phases.length];
		final Statement[] emptyArray = new Statement[0];
		for (int i = 0; i < phases.length; i++) {
			final Expression ifCon = genComparePhaseCounter(i, pcName, bl);
			final Statement[] outerIfBodySmt = new Statement[] { genOuterIfBody(automaton, pcName, phases[i], bl) };
			final IfStatement ifStatement = new IfStatement(bl, ifCon, outerIfBodySmt, emptyArray);
			statements[i] = ifStatement;
		}
		return joinIfSmts(statements, bl);
	}

	private List<Statement> genStateVarsAssign(final BoogieLocation bl) {
		final List<Statement> statements = new ArrayList<>();
		for (final String stateVar : mStateVars.keySet()) {
			final VariableLHS lhsVar = new VariableLHS(bl, stateVar);
			final IdentifierExpression rhs = new IdentifierExpression(bl, getPrimedVar(stateVar));
			final LeftHandSide[] lhs = new LeftHandSide[1];
			lhs[0] = lhsVar;
			final Expression[] expr = new Expression[1];
			expr[0] = rhs;
			final AssignmentStatement assignment = new AssignmentStatement(bl, lhs, expr);
			statements.add(assignment);
		}
		return statements;
	}

	@SafeVarargs
	private static ReqCheck createReqCheck(final Check.Spec reqSpec,
			final Entry<PatternType, PhaseEventAutomata>... subset) {
		final PatternType[] reqs = new PatternType[subset.length];
		for (int i = 0; i < subset.length; ++i) {
			reqs[i] = subset[i].getKey();
		}
		return createReqCheck(reqSpec, reqs);
	}

	private static ReqCheck createReqCheck(final Check.Spec reqSpec, final PatternType... req) {
		if (req == null || req.length == 0) {
			throw new IllegalArgumentException("req cannot be null or empty");
		}
		return new ReqCheck(reqSpec, req);
	}

	private List<Statement> genCheckConsistency(final BoogieLocation bl) {
		if (!mCheckConsistency) {
			return Collections.emptyList();
		}
		final ReqCheck check = new ReqCheck(Spec.CONSISTENCY);
		final Expression expr = ExpressionFactory.createBooleanLiteral(bl, false);
		return Collections.singletonList(createAssert(expr, check, "CONSISTENCY"));
	}

	private Statement genAssertRTInconsistency(final Entry<PatternType, PhaseEventAutomata>[] subset,
			final BoogieLocation bl, final CDD primedInvariant) {
		final Set<PhaseEventAutomata> automataSet =
				Arrays.stream(subset).map(a -> a.getValue()).collect(Collectors.toSet());
		assert automataSet.size() == subset.length;
		final PhaseEventAutomata[] automata = automataSet.toArray(new PhaseEventAutomata[subset.length]);
		final Expression expr = new ConditionGenerator(getPrimedVars(), automata, bl, primedInvariant).getResult();
		final ReqCheck check = createReqCheck(Spec.RTINCONSISTENT, subset);

		if (expr == null) {
			if (mReportTrivialConsistency) {
				final AssertStatement fakeElem = createAssert(ExpressionFactory.createBooleanLiteral(bl, true), check,
						"RTINCONSISTENT_" + getAssertLabel(subset));
				mPeaResultUtil.intrinsicRtConsistencySuccess(fakeElem);
			}
			return null;
		}

		return createAssert(expr, check, "RTINCONSISTENT_" + getAssertLabel(subset));
	}

	private static String getAssertLabel(final Entry<PatternType, PhaseEventAutomata>[] subset) {
		final StringBuilder sb = new StringBuilder();
		for (final Entry<PatternType, PhaseEventAutomata> entry : subset) {
			sb.append(entry.getValue().getName() + "_");
		}
		return sb.toString();
	}

	/**
	 * Generate the assertion that is violated if the requirement represented by the given automaton is non-vacuous. The
	 * assertion expresses that the automaton always stays in the early phases and never reaches the last phase. It may
	 * be false if all phases of the automaton are part of the last phase, in which case this function returns null.
	 *
	 * @param req
	 *            The requirement for which vacuity is checked.
	 * @param aut
	 *            The automaton for which vacuity is checked.
	 * @param bl
	 *            A boogie location used for all statements.
	 * @return The assertion for non-vacousness or null if the assertion would be false.
	 */
	private Statement genAssertNonVacuous(final PatternType req, final PhaseEventAutomata aut,
			final BoogieLocation bl) {
		final Phase[] phases = aut.getPhases();

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
		while (1 << pnr <= maxBits) {
			pnr++;
		}

		// check that one of those phases is eventually reached.
		final List<Expression> checkReached = new ArrayList<>();
		for (int i = 0; i < phases.length; i++) {
			final PhaseBits bits = phases[i].getPhaseBits();
			if (bits == null || (bits.getActive() & 1 << pnr - 1) == 0) {
				checkReached.add(genComparePhaseCounter(i, getPcName(aut), bl));
			}
		}
		if (checkReached.isEmpty()) {
			return null;
		}
		final Expression disjunction = genDisjunction(checkReached, bl);
		final ReqCheck check = createReqCheck(Spec.VACUOUS, req);
		final String label = "VACUOUS_" + aut.getName();
		return createAssert(disjunction, check, label);
	}

	private static AssertStatement createAssert(final Expression expr, final ReqCheck check, final String label) {
		final ReqLocation loc = new ReqLocation(check);
		final NamedAttribute[] attr =
				new NamedAttribute[] { new NamedAttribute(loc, "check_" + label, new Expression[] {}) };
		final AssertStatement rtr = new AssertStatement(loc, attr, expr);
		check.annotate(rtr);
		return rtr;
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
	private Statement[] genWhileBody(final BoogieLocation bl) {
		final List<Statement> stmtList = new ArrayList<>();
		stmtList.addAll(Arrays.asList(genDelay(bl)));

		for (final Entry<PatternType, PhaseEventAutomata> entry : mReq2Automata.entrySet()) {
			stmtList.addAll(genInvariantGuards(entry.getValue(), getPcName(entry.getValue()), bl));
		}

		stmtList.addAll(genChecksRTInconsistency(bl));
		stmtList.addAll(genChecksNonVacuity(bl));
		stmtList.addAll(genCheckConsistency(bl));

		for (final Entry<PatternType, PhaseEventAutomata> entry : mReq2Automata.entrySet()) {
			stmtList.add(genOuterIfTransition(entry.getValue(), getPcName(entry.getValue()), bl));
		}

		if (!mStateVars.isEmpty()) {
			final List<Statement> stateVarsAssigns = genStateVarsAssign(bl);
			for (int i = 0; i < stateVarsAssigns.size(); i++) {
				stmtList.add(stateVarsAssigns.get(i));
			}
		}

		return stmtList.toArray(new Statement[stmtList.size()]);
	}

	private List<Statement> genChecksNonVacuity(final BoogieLocation bl) {
		if (!mCheckVacuity) {
			return Collections.emptyList();
		}

		final List<Statement> stmtList = new ArrayList<>();
		for (final Entry<PatternType, PhaseEventAutomata> entry : mReq2Automata.entrySet()) {
			final Statement assertStmt = genAssertNonVacuous(entry.getKey(), entry.getValue(), bl);
			if (assertStmt != null) {
				stmtList.add(assertStmt);
			}

		}
		return stmtList;
	}

	private List<Statement> genChecksRTInconsistency(final BoogieLocation bl) {
		if (mCombinationNum <= 1) {
			return Collections.emptyList();
		}

		// get all automata that are invariant, prime their state invariant and conjugate the primed state invariant
		final CDD primedStateInvariant = getPrimedStateInvariant();

		// get all automata that are not invariant, i.e. have more than 1 phase
		final List<Entry<PatternType, PhaseEventAutomata>> entries = mReq2Automata.entrySet().stream()
				.filter(a -> a.getValue().getPhases().length != 1).collect(Collectors.toList());

		final int count = entries.size();
		mLogger.info((mReq2Automata.size() - count) + " requirements are invariant");
		final int actualCombinationNum = mCombinationNum <= count ? mCombinationNum : count;
		final List<Statement> stmtList = new ArrayList<>();
		@SuppressWarnings("unchecked")
		final List<Entry<PatternType, PhaseEventAutomata>[]> subsets = CrossProducts
				.subArrays(entries.toArray(new Entry[count]), actualCombinationNum, new Entry[actualCombinationNum]);
		int subsetsSize = subsets.size();
		if (subsetsSize > 10000) {
			mLogger.warn("Computing rt-inconsistency assertions for " + subsetsSize
					+ " subsets, this might take a while...");
		} else {
			mLogger.info("Computing rt-inconsistency assertions for " + subsetsSize + " subsets");
		}

		for (final Entry<PatternType, PhaseEventAutomata>[] subset : subsets) {
			subsetsSize--;
			if (subsetsSize % 1000 == 0 && !mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(),
						"Computing rt-inconsistency assertions, still " + subsetsSize + " left");
			}
			final Statement assertStmt = genAssertRTInconsistency(subset, bl, primedStateInvariant);
			if (assertStmt != null) {
				stmtList.add(assertStmt);
			}
		}
		return stmtList;
	}

	private CDD getPrimedStateInvariant() {
		final Optional<CDD> possiblePrimedStateInvariant =
				mReq2Automata.entrySet().stream().filter(a -> a.getValue().getPhases().length == 1)
						.map(a -> a.getValue().getPhases()[0].getStateInvariant().prime()).reduce((a, b) -> a.and(b));
		final CDD actualPrimedStateInvariant;
		if (possiblePrimedStateInvariant.isPresent()) {
			actualPrimedStateInvariant = possiblePrimedStateInvariant.get();
		} else {
			actualPrimedStateInvariant = CDD.TRUE;
		}
		return actualPrimedStateInvariant;
	}

	/**
	 * Create the main loop of the pea product. This is a huge while statement that contains all transitions of all
	 * components. This procedure calls {@link genWhileBody} to create the statements of the main loop.
	 *
	 * @param bl
	 *            Location of the procedure body.
	 * @return The while-statement.
	 */
	private Statement genWhileStmt(final BoogieLocation bl) {
		return new WhileStatement(bl, new WildcardExpression(bl), new LoopInvariantSpecification[0], genWhileBody(bl));
	}

	private Expression genPcExpr(final PhaseEventAutomata aut, final BoogieLocation bl) {
		final Phase[] phases = aut.getPhases();
		final Phase[] initialPhases = aut.getInit();
		// determine initial phases
		for (int i = 0; i < phases.length; i++) {

			for (int j = 0; j < initialPhases.length; j++) {
				if (phases[i].getName().equals(initialPhases[j].getName())) {
					phases[i].setInit(true);
					break;
				}
			}
		}
		final String pcName = getPcName(aut);
		// construct or over initial phases
		Expression acc = null;
		for (int i = 0; i < phases.length; i++) {
			if (!phases[i].isInit) {
				continue;
			}
			final IdentifierExpression identifier = ExpressionFactory.constructIdentifierExpression(bl,
					BoogieType.TYPE_INT, pcName, DeclarationInformation.DECLARATIONINFO_GLOBAL);
			final Expression current = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.COMPEQ,
					identifier, ExpressionFactory.createIntegerLiteral(bl, Integer.toString(i)));
			if (acc == null) {
				acc = current;
			} else {
				acc = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.LOGICOR, acc, current);
			}
		}
		return mNormalFormTransformer.toNnf(acc);
	}

	private List<Statement> genInitialPhasesStmts(final BoogieLocation bl) {
		final List<Statement> stmts = new ArrayList<>();
		for (final Entry<PatternType, PhaseEventAutomata> entry : mReq2Automata.entrySet()) {
			final PhaseEventAutomata aut = entry.getValue();
			stmts.add(new HavocStatement(bl, new VariableLHS[] { new VariableLHS(bl, getPcName(aut)) }));
			stmts.add(new AssumeStatement(bl, genPcExpr(aut, bl)));
		}
		return stmts;
	}

	private List<Statement> genClockInitStmts(final BoogieLocation bl) {
		if (mClockIds.isEmpty()) {
			return Collections.emptyList();
		}
		final List<Statement> stmts = new ArrayList<>();
		for (final String clkId : mClockIds) {
			final IdentifierExpression id = ExpressionFactory.constructIdentifierExpression(bl, BoogieType.TYPE_REAL,
					clkId, DeclarationInformation.DECLARATIONINFO_GLOBAL);
			final RealLiteral real = ExpressionFactory.createRealLiteral(bl, "0.0");
			stmts.add(new HavocStatement(bl, new VariableLHS[] { new VariableLHS(bl, clkId) }));
			stmts.add(new AssumeStatement(bl,
					ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.COMPEQ, id, real)));
		}
		return stmts;
	}

	/**
	 * One assignment is initialized (only as an example). The genWhileSmt method is called.
	 *
	 * @param bl
	 *            Location of the procedure body.
	 * @param init
	 * @return Statements of the procedure body which includes one assignment and one while-statement.
	 */
	private Statement[] generateProcedureBodyStmts(final BoogieLocation bl, final List<InitializationPattern> init) {
		final List<Statement> statements = new ArrayList<>();
		statements.addAll(genInitialPhasesStmts(bl));
		statements.addAll(genClockInitStmts(bl));
		statements.addAll(genConstInitStmts(bl, init));
		statements.add(genWhileStmt(bl));
		return statements.toArray(new Statement[statements.size()]);
	}

	private static List<Statement> genConstInitStmts(final BoogieLocation bl, final List<InitializationPattern> init) {
		final List<InitializationPattern> constInits =
				init.stream().filter(a -> a.getCategory() == VariableCategory.CONST).collect(Collectors.toList());
		if (constInits.isEmpty()) {
			return Collections.emptyList();
		}
		final List<Statement> statements = new ArrayList<>(constInits.size());
		for (final InitializationPattern constInit : constInits) {
			final String id = constInit.getId();
			final Expression val = constInit.getExpression();
			statements.add(genAssignmentStmt(bl, id, val));
			statements.add(genAssignmentStmt(bl, getPrimedVar(id), val));
		}
		return statements;
	}

	private static AssignmentStatement genAssignmentStmt(final BoogieLocation bl, final String id,
			final Expression val) {
		return new AssignmentStatement(bl, new LeftHandSide[] { new VariableLHS(bl, id) }, new Expression[] { val });
	}

	/**
	 * The procedure statement is initialized. It is deployed to the unit. The unit is sent to the print process. The
	 * result is a Boogie text file.
	 *
	 * @param init
	 */
	private Declaration generateProcedures(final List<InitializationPattern> init) {
		final BoogieLocation bl = mUnitLocation;
		final VariableDeclaration[] localVars = new VariableDeclaration[0];
		final Body body = new Body(bl, localVars, generateProcedureBodyStmts(bl, init));
		final List<String> modifiedVarsList = new ArrayList<>();
		modifiedVarsList.addAll(mClockIds);
		modifiedVarsList.addAll(mPcIds);
		modifiedVarsList.add("delta");
		modifiedVarsList.addAll(mConstVars.keySet());
		modifiedVarsList.addAll(mStateVars.keySet());
		modifiedVarsList.addAll(mPrimedVars.keySet());
		modifiedVarsList.addAll(mEventVars.keySet());

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
		return new Procedure(bl, attribute, "myProcedure", typeParams, inParams, outParams, modArray, body);
	}
}
