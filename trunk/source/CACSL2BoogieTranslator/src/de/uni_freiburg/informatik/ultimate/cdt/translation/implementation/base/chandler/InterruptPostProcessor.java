/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotations.ISRLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptServiceRoutines;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptTranslationMode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Transform an Interrupt-driven program into a thread-based program by either introducing one thread for each ISR
 * (realization 1), introducing only one thread that handles all ISR (realization 2) or introducing one thread per ISR
 * and also adding fork and join statements for the corresponding thread to the ISR enabled/disabled methods. This is
 * done by post-processing the Boogie unit and adding additional declarations and annotating existing procedures with
 * auxiliary code.
 */
public class InterruptPostProcessor implements IPostProcessor {

	private static final boolean ADD_ISR_LABELS = true;

	private final ILogger mLogger;

	private final ProcedureManager mProcedureManager;

	private final CHandler mCHandler;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final ExpressionTranslation mExpressionTranslation;

	private final ILocation mIgnoreLoc = LocationFactory.createIgnoreCLocation();

	private final InterruptTranslationMode mTranslationMode;

	private final InterruptServiceRoutines mISR;

	private Map<Integer, IdentifierExpression> mAuxVarExpressions = null;

	private final List<Statement> mAdditionalInitializations = new ArrayList<>();
	private final ISRLoopSearchVisitor mLoopSearchVisitor;

	public InterruptPostProcessor(final ILogger logger, final TranslationSettings settings,
			final ProcedureManager procedureManager, final CHandler chandler, final AuxVarInfoBuilder auxVarInfoBuilder,
			final ExpressionTranslation expressionTranslation, final InterruptServiceRoutines isrs) {
		mLogger = logger;
		mProcedureManager = procedureManager;
		mCHandler = chandler;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mExpressionTranslation = expressionTranslation;
		mTranslationMode = settings.interruptTranslationMode();
		mISR = isrs;
		mLoopSearchVisitor = new ISRLoopSearchVisitor(isrs);
	}

	@Override
	public List<Declaration> postProcess(final ILocation loc, final IASTNode hook,
			final List<Statement> additionalInitializations) {
		// TODO: Add exclusion of these two settings directly to settings
		final ArrayList<Declaration> decl = new ArrayList<>();
		final var realization3 = mTranslationMode == InterruptTranslationMode.ONE_THREAD_PER_ISR_FORK_JOIN;

		// Get the ghost variables that signal whether an ISR is enabled
		mAuxVarExpressions = constructAuxVarExpressions(mISR.getISRMap().keySet());

		mLogger.info("Verify IDP with %d ISRs", mAuxVarExpressions.size());

		// Add thread gpio procedures
		final var threadGpioProcedureMap = constructThreadGpioProc();
		final var threadGpioProcedures = new ArrayList<>(threadGpioProcedureMap.values());
		decl.addAll(threadGpioProcedures);

		// Add fork statements to the main procedure
		if (!realization3) {
			addForksToProcedure(mISR.getMainProcedure(), threadGpioProcedures);
		}

		// Add atomic block and variable assignment true to request enabled functions
		final var lhsMap = getVariableLHSs();
		annotateRequestProcedures(lhsMap, mISR.getRequestEnable(), true);

		// Add fork statements in request enable procedure instead of the main procedure
		if (realization3) {
			addForksToRequestEnable(mISR.getRequestEnable(), threadGpioProcedureMap);
		}
		// Add atomic block and variable assignment false to request disabled functions if
		annotateRequestProcedures(lhsMap, mISR.getRequestDisable(), false);

		// Add join statements to request disable procedure
		if (realization3) {
			addJoinsToRequestDisable(mISR.getRequestDisable());
		}

		// Add atomic block and variable assignment true to request enabled all function
		annotateRequestAllProcedures(lhsMap.values(), mISR.getRequestEnableAll(), true);

		if (realization3) {
			addForksToRequestEnableAll(mISR.getRequestEnableAll(), threadGpioProcedureMap);
		}

		// Add interrupt enabled variable declarations
		decl.addAll(constructAuxVarEnableDeclarations());

		mAdditionalInitializations.add(constructAuxVarEnabledInitializations(lhsMap.values()));

		return decl;
	}

	private void addForksToProcedure(final Procedure mainProcedure, final List<Procedure> threadGpioProcedures) {
		final List<Statement> newBlock = constructForkStatements(mainProcedure, threadGpioProcedures, -1);
		final var body = mainProcedure.getBody();
		newBlock.addAll(Arrays.asList(body.getBlock()));
		body.setBlock(newBlock.toArray(new Statement[0]));
	}

	private void addForksToRequestEnableAll(final Procedure mainProcedure,
			final Map<Integer, Procedure> threadGpioProceduresMap) {
		if (mainProcedure == null) {
			return;
		}
		final var statements = new ArrayList<Statement>();
		for (final Entry<Integer, Procedure> entry : threadGpioProceduresMap.entrySet()) {
			final var irq = entry.getKey();
			final var proc = entry.getValue();
			final var fork = constructForkStatements(mainProcedure, List.of(proc), -irq);
			final var idExpr = mAuxVarExpressions.get(irq);
			assert idExpr != null;
			final var ifStmt = constructForkIfStatement(idExpr, fork, true);
			statements.add(ifStmt);
		}
		final var body = mainProcedure.getBody();
		statements.addAll(Arrays.asList(body.getBlock()));
		body.setBlock(statements.toArray(new Statement[0]));
	}

	private void addForksToRequestEnable(final Map<Integer, Procedure> intEnabledProcedures,
			final Map<Integer, Procedure> threadGpioProceduresMap) {
		for (final Entry<Integer, Procedure> entry : intEnabledProcedures.entrySet()) {
			final var irq = entry.getKey();
			final var proc = entry.getValue();
			final var threadGpioProcedure = threadGpioProceduresMap.get(irq);
			assert threadGpioProcedure != null;

			final var thrNum = -irq;
			final List<Statement> fork = constructForkStatements(proc, List.of(threadGpioProcedure), thrNum);

			final var idExpr = mAuxVarExpressions.get(irq);
			assert idExpr != null;
			final var newBlock = new ArrayList<>(List.of(constructForkIfStatement(idExpr, fork, true)));
			final var body = proc.getBody();
			newBlock.addAll(Arrays.asList(body.getBlock()));
			body.setBlock(newBlock.toArray(new Statement[0]));
		}
	}

	private void addJoinsToRequestDisable(final Map<Integer, Procedure> intDisabledProcedures) {
		for (final Entry<Integer, Procedure> entry : intDisabledProcedures.entrySet()) {
			final var irq = entry.getKey();
			final var proc = entry.getValue();
			final List<Statement> join = constructJoinStatement(proc, -irq);
			final var idExpr = mAuxVarExpressions.get(irq);
			assert idExpr != null;
			final var newBlock = new ArrayList<>(List.of(constructForkIfStatement(idExpr, join, false)));
			final var body = proc.getBody();
			newBlock.addAll(Arrays.asList(body.getBlock()));
			body.setBlock(newBlock.toArray(new Statement[0]));
		}
	}

	private List<Statement> constructForkStatements(final Procedure mainProcedure,
			final List<Procedure> threadGpioProcedures, final Integer threadNum) {
		mProcedureManager.beginProcedureScope(mCHandler,
				mProcedureManager.getProcedureInfo(mainProcedure.getIdentifier()));
		assert threadNum <= 0;
		final var forkStatements = new ArrayList<Statement>();
		final String threadNumString = String.valueOf(threadNum);
		final var threadId = ExpressionFactory.createIntegerLiteral(mIgnoreLoc, threadNumString);
		for (final Procedure procedure : threadGpioProcedures) {
			final var fs = new ForkStatement(mIgnoreLoc, new Expression[] { threadId }, procedure.getIdentifier(),
					new Expression[0]);
			forkStatements.add(fs);
			mProcedureManager.registerForkStatement(fs);
		}
		mProcedureManager.endProcedureScope(mCHandler);
		return forkStatements;
	}

	private List<Statement> constructJoinStatement(final Procedure mainProcedure, final int threadNum) {
		mProcedureManager.beginProcedureScope(mCHandler,
				mProcedureManager.getProcedureInfo(mainProcedure.getIdentifier()));
		assert threadNum <= 0;
		final var joinStatements = new ArrayList<Statement>();
		final String threadNumString = String.valueOf(threadNum);
		final var threadId = ExpressionFactory.createIntegerLiteral(mIgnoreLoc, threadNumString);
		final var js = new JoinStatement(mIgnoreLoc, new Expression[] { threadId }, new VariableLHS[0]);
		joinStatements.add(js);
		mProcedureManager.endProcedureScope(mCHandler);
		return joinStatements;
	}

	private Statement constructForkIfStatement(final IdentifierExpression idExpr, final List<Statement> statements,
			final boolean negated) {
		Expression condition = idExpr;
		if (negated) {
			condition = ExpressionFactory.constructUnaryExpression(mIgnoreLoc,
					de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator.LOGICNEG,
					new IdentifierExpression(mIgnoreLoc, BoogieType.TYPE_BOOL, idExpr.getIdentifier(),
							DeclarationInformation.DECLARATIONINFO_GLOBAL));
		}
		return StatementFactory.constructIfStatement(mIgnoreLoc, condition, statements);
	}

	private Set<Declaration> constructAuxVarEnableDeclarations() {
		final var declarations = new HashSet<Declaration>();
		final var astType = new PrimitiveType(mIgnoreLoc, "bool");
		for (final IdentifierExpression identifierExpression : mAuxVarExpressions.values()) {
			final var decl = new VariableDeclaration(mIgnoreLoc, new Attribute[0], new VarList[] {
					new VarList(mIgnoreLoc, new String[] { identifierExpression.getIdentifier() }, astType) });
			declarations.add(decl);
		}
		return declarations;
	}

	private Map<Integer, IdentifierExpression> constructAuxVarExpressions(final Collection<Integer> identifiers) {
		final var idExpressions = new HashMap<Integer, IdentifierExpression>();
		for (final Integer irq : identifiers) {
			final var id = "#isr_" + irq + "_enabled";
			final var enabledExpr = ExpressionFactory.constructIdentifierExpression(mIgnoreLoc, BoogieType.TYPE_BOOL,
					id, DeclarationInformation.DECLARATIONINFO_GLOBAL);
			idExpressions.put(irq, enabledExpr);
		}
		return idExpressions;
	}

	private Statement constructAuxVarEnabledInitializations(final Collection<VariableLHS> leftHandSides) {
		final Expression assignment = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, false);
		final Expression[] assignments = new Expression[leftHandSides.size()];
		Arrays.fill(assignments, assignment);
		return StatementFactory.constructAssignmentStatement(mIgnoreLoc, leftHandSides.toArray(new LeftHandSide[0]),
				assignments);
	}

	private void annotateRequestProcedures(final Map<Integer, VariableLHS> lhsMap,
			final Map<Integer, Procedure> intEnabledProcedures, final boolean enabled) {
		if (intEnabledProcedures == null) {
			return;
		}
		final String func = enabled ? " enable " : " disable ";
		for (final Entry<Integer, VariableLHS> entry : lhsMap.entrySet()) {
			final var irq = entry.getKey();

			mLogger.info("Adding IRQ" + func + "function for ISR " + irq);

			final var lhs = entry.getValue();
			final var intEnableProcedure = intEnabledProcedures.get(irq);
			if (intEnableProcedure == null) {
				mLogger.warn("There exists no IRQ" + func + "function for ISR " + irq);
				continue;
			}
			annotateAuxVarAssignment(intEnableProcedure, enabled, List.of(lhs));
		}
	}

	private void annotateRequestAllProcedures(final Collection<VariableLHS> lhs, final Procedure intEnabledProcedure,
			final boolean enabled) {
		if (intEnabledProcedure == null) {
			return;
		}
		annotateAuxVarAssignment(intEnabledProcedure, enabled, lhs);
	}

	private void annotateAuxVarAssignment(final Procedure intEnableProcedure, final boolean newValue,
			final Collection<VariableLHS> intEnabledLhs) {
		if (intEnableProcedure == null) {
			return;
		}
		mProcedureManager.beginProcedureScope(mCHandler,
				mProcedureManager.getProcedureInfo(intEnableProcedure.getIdentifier()));
		final var body = intEnableProcedure.getBody();
		final var block = body.getBlock();
		final var assignments =
				intEnabledLhs.stream()
						.map(i -> StatementFactory.constructSingleAssignmentStatement(mIgnoreLoc, i,
								ExpressionFactory.createBooleanLiteral(mIgnoreLoc, newValue)))
						.collect(Collectors.toList());
		final var newBlock = new ArrayList<>(Arrays.asList(block));
		newBlock.addAll(assignments);
		final var atomic = StatementFactory.constructAtomicStatement(mIgnoreLoc, newBlock);
		final var newBody = mProcedureManager.constructBody(mIgnoreLoc, new VariableDeclaration[0],
				new Statement[] { atomic }, intEnableProcedure.getIdentifier());
		body.setBlock(newBody.getBlock());
		mProcedureManager.endProcedureScope(mCHandler);
	}

	private Map<Integer, Procedure> constructThreadGpioProc() {
		assert mTranslationMode != InterruptTranslationMode.NONE : "The chosen interrupt translation mode is NONE";
		final var procedures = new HashMap<Integer, Procedure>();
		final var oneThreadPerISR = mTranslationMode == InterruptTranslationMode.ONE_THREAD_PER_ISR
				|| mTranslationMode == InterruptTranslationMode.ONE_THREAD_PER_ISR_FORK_JOIN;
		if (oneThreadPerISR) {
			mLogger.info("Source-to-source translation of interrupt program with realization 1");
			final var isrGpios = mISR.getISRMap().entrySet();
			for (final Entry<Integer, Procedure> entry : isrGpios) {
				final var irq = entry.getKey();
				final var isr = entry.getValue();
				final var procId = isr.getIdentifier();
				final var idExpression = mAuxVarExpressions.get(irq);
				assert idExpression != null : "There exists no identifier expression for the IRQ: " + irq;
				procedures.put(irq, constructOneInterruptThreadGpioProc(procId, idExpression, irq));
			}
		} else {
			mLogger.info("Source-to-source translation of interrupt program with realization 2");
			procedures.put(-1, constructAllInterruptsThreadGpioProc());
		}
		return procedures;
	}

	// Realization 1
	private Procedure constructOneInterruptThreadGpioProc(final String identifier,
			final IdentifierExpression threadEnabledId, final Integer irq) {
		final var procName = constructThreadGpioID(identifier, irq);

		mLogger.info("Adding auxilliary ISR-Thread function " + procName + " for ISR " + identifier);

		final var declaration = new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0],
				new VarList[0], new Specification[0], null);
		mProcedureManager.beginCustomProcedure(mCHandler, mIgnoreLoc, procName, declaration);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final var whileStmt = constructIsrWhileLoop(identifier, threadEnabledId, irq);
		builder.addStatement(whileStmt);
		final var body = mProcedureManager.constructBody(mIgnoreLoc,
				builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
				builder.getStatements().toArray(new Statement[builder.getStatements().size()]), procName);
		mProcedureManager.endCustomProcedure(mCHandler, procName);
		return new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0], new VarList[0],
				null, body);
	}

	// Realization 2

	private Procedure constructAllInterruptsThreadGpioProc() {
		final var procName = constructThreadGpioID("all", 0);
		mLogger.info("Adding auxilliary ISR-Thread function " + procName);
		final var declaration = new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0],
				new VarList[0], new Specification[0], null);
		mProcedureManager.beginCustomProcedure(mCHandler, mIgnoreLoc, procName, declaration);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final var nondetVarInfo = getHavocAuxVar(builder);
		final var whileStmt = constructAllIsrWhileLoop(nondetVarInfo);
		builder.addStatement(whileStmt);
		final var body = mProcedureManager.constructBody(mIgnoreLoc,
				builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
				builder.getStatements().toArray(new Statement[builder.getStatements().size()]), procName);
		mProcedureManager.endCustomProcedure(mCHandler, procName);
		return new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0], new VarList[0],
				null, body);
	}

	private AuxVarInfo getHavocAuxVar(final ExpressionResultBuilder builder) {
		final CPrimitive cType = new CPrimitive(CPrimitives.BOOL);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(mIgnoreLoc, cType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvarinfo);
		builder.addStatements(getHavocBoolStatements(auxvarinfo));

		return auxvarinfo;
	}

	private List<Statement> getHavocBoolStatements(final AuxVarInfo auxvarinfo) {
		final CPrimitive cType = new CPrimitive(CPrimitives.BOOL);
		final var statements = new ArrayList<Statement>();
		statements.add(new HavocStatement(mIgnoreLoc, new VariableLHS[] { auxvarinfo.getLhs() }));

		final Expression isZero =
				ExpressionFactory.newBinaryExpression(mIgnoreLoc, Operator.COMPEQ, auxvarinfo.getExp(),
						mExpressionTranslation.constructLiteralForIntegerType(mIgnoreLoc, cType, BigInteger.ZERO));
		final Expression isOne = ExpressionFactory.newBinaryExpression(mIgnoreLoc, Operator.COMPEQ, auxvarinfo.getExp(),
				mExpressionTranslation.constructLiteralForIntegerType(mIgnoreLoc, cType, BigInteger.ONE));
		statements.add(new AssumeStatement(mIgnoreLoc, ExpressionFactory.or(mIgnoreLoc, List.of(isZero, isOne))));
		return statements;
	}

	private Statement constructIsrWhileLoop(final String identifier, final IdentifierExpression threadEnabledId,
			final Integer isrNum) {
		final var enabledExpr = threadEnabledId;
		final var ifStmt = getIfStatement(identifier, enabledExpr, isrNum);
		final var block = getIsrBlock(ifStmt, identifier);
		final var forkJoin = mTranslationMode == InterruptTranslationMode.ONE_THREAD_PER_ISR_FORK_JOIN;
		final var while_condition = forkJoin ? enabledExpr : ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, while_condition, new LoopInvariantSpecification[0], block);
	}

	private Statement constructAllIsrWhileLoop(final AuxVarInfo auxVarInfo) {
		final var atomicStatements = new ArrayList<Statement>();
		for (final Entry<Integer, Procedure> entry : mISR.getISRMap().entrySet()) {
			final var ifStatements = new ArrayList<Statement>();
			final var boolHavoc = getHavocBoolStatements(auxVarInfo);
			ifStatements.addAll(boolHavoc);
			final var irq = entry.getKey();
			final var identifier = entry.getValue().getIdentifier();
			final var threadEnabledId = mAuxVarExpressions.get(irq);
			final var enabledExpression = getEnabledExpression(threadEnabledId, auxVarInfo);
			assert threadEnabledId != null : "There exists no IdentifierExpression of ISR with IRQ: " + irq;
			ifStatements.add(getIfStatement(identifier, enabledExpression, irq));
			final var block = getIsrBlock(ifStatements, identifier);
			atomicStatements.addAll(block);
		}
		final var alwaysTrue = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, alwaysTrue, new LoopInvariantSpecification[0],
				atomicStatements.toArray(new Statement[0]));
	}

	private List<Statement> getIsrBlock(final List<Statement> ifStatements, final String identifier) {
		if (ADD_ISR_LABELS && mLoopSearchVisitor.containsLoop(identifier)) {
			return ifStatements;
		}
		return List.of(StatementFactory.constructAtomicStatement(mIgnoreLoc, ifStatements));
	}

	private Statement[] getIsrBlock(final Statement ifStatement, final String identifier) {
		if (ADD_ISR_LABELS && mLoopSearchVisitor.containsLoop(identifier)) {
			return new Statement[] { ifStatement };
		}
		return new Statement[] { StatementFactory.constructAtomicStatement(mIgnoreLoc, List.of(ifStatement)) };
	}

	private Statement getIfStatement(final String identifier, final Expression enabledExpr, final int id) {
		final var interruptAnnotation = new InterruptAnnotations(ISRLocation.ENTRY, id);
		final var then = StatementFactory.constructCallStatement(mIgnoreLoc, false, new VariableLHS[0], identifier,
				new Expression[0]);
		if (ADD_ISR_LABELS && mLoopSearchVisitor.containsLoop(identifier)) {
			mLogger.info("Add interrupt labels to call of function: " + identifier);
			final var ifStmt = StatementFactory.constructIfStatement(mIgnoreLoc, enabledExpr,
					labelISRStatement(then, id), new Statement[0]);
			// TODO: Handle annotation for contains case
			interruptAnnotation.annotate(ifStmt);
			return ifStmt;
		}
		return StatementFactory.constructIfStatement(mIgnoreLoc, enabledExpr, new Statement[] { then },
				new Statement[0]);
	}

	private Statement[] labelISRStatement(final Statement isrStatement, final Integer isrId) {
		final var labelName = "~isr" + isrId;
		final var isrNumAttribute = new NamedAttribute(mIgnoreLoc, Integer.toString(isrId), new Expression[0]);
		final var isrAttribute = new NamedAttribute(mIgnoreLoc, "isr_label", new Expression[0]);
		final var entryAttribute = new NamedAttribute(mIgnoreLoc, "entry", new Expression[0]);
		final var exitAttribute = new NamedAttribute(mIgnoreLoc, "exit", new Expression[0]);
		final var entryLabel = new Label(mIgnoreLoc, labelName + "Entry",
				new NamedAttribute[] { isrAttribute, entryAttribute, isrNumAttribute });
		final var exitLabel = new Label(mIgnoreLoc, labelName + "Exit",
				new NamedAttribute[] { isrAttribute, exitAttribute, isrNumAttribute });
		return new Statement[] { entryLabel, isrStatement, exitLabel };
	}

	private Expression getEnabledExpression(final IdentifierExpression threadEnabledId, final AuxVarInfo auxVarInfo) {
		final CPrimitive cType = new CPrimitive(CPrimitives.BOOL);
		final Expression isOne = ExpressionFactory.newBinaryExpression(mIgnoreLoc, Operator.COMPEQ, auxVarInfo.getExp(),
				mExpressionTranslation.constructLiteralForIntegerType(mIgnoreLoc, cType, BigInteger.ONE));
		return ExpressionFactory.and(mIgnoreLoc, List.of(threadEnabledId, isOne));
	}

	private String constructThreadGpioID(final String identifier, final Integer irq) {
		return "#isr_" + irq + "_" + identifier + "_thread";
	}

	private Map<Integer, VariableLHS> getVariableLHSs() {
		return mAuxVarExpressions.entrySet().stream()
				.collect(Collectors.toMap(Entry::getKey,
						e -> ExpressionFactory.constructVariableLHS(mIgnoreLoc, BoogieType.TYPE_BOOL,
								e.getValue().getIdentifier(), DeclarationInformation.DECLARATIONINFO_GLOBAL)));
	}

	public List<Statement> getAdditionalInitializations() {
		return mAdditionalInitializations;
	}

	private static class ISRLoopSearchVisitor {

		private final InterruptServiceRoutines mISR;
		private final Map<String, Boolean> mContainsLoop;

		public ISRLoopSearchVisitor(final InterruptServiceRoutines interruptServiceRoutines) {
			mISR = interruptServiceRoutines;
			mContainsLoop = visitISRs();
		}

		private Map<String, Boolean> visitISRs() {
			final var containsLoopMap = new HashMap<String, Boolean>();
			for (final Procedure proc : mISR.getISRMap().values()) {
				final var containsLoop = visitProc(proc);
				containsLoopMap.put(proc.getIdentifier(), true);
			}
			return containsLoopMap;
		}

		private Boolean visitProc(final Procedure proc) {
			return visitBody(proc.getBody());
		}

		private Boolean visitBody(final Body body) {
			return visitBlock(body.getBlock());
		}

		private Boolean visitBlock(final Statement[] statements) {
			for (final Statement statement : statements) {
				if (visitStatement(statement)) {
					return true;
				}
			}
			return false;
		}

		private Boolean visitStatement(final Statement statement) {
			// TODO: Add handling for call statements
			if (statement instanceof WhileStatement || statement instanceof CallStatement
					|| statement instanceof ForkStatement || statement instanceof GotoStatement
					|| statement instanceof JoinStatement) {
				return true;
			} else if (statement instanceof final IfStatement ifStatement) {
				return visitBlock(ifStatement.getThenPart()) || visitBlock(ifStatement.getElsePart());
			} else if (statement instanceof final AtomicStatement atomicStatement) {
				return visitBlock(atomicStatement.getBody());
			}
			return false;
		}

		public Boolean containsLoop(final String identifier) {
			final var contains = mContainsLoop.get(identifier);
			assert contains != null;
			return contains;
		}
	}
}
