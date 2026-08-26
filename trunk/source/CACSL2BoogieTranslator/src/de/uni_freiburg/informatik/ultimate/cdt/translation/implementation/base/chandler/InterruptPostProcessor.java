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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation.ISRLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptTranslationMode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptMaskingFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptServiceFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.InterruptRequest;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.InterruptRequestHandler;
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

	private final String mEntryFunction;

	private final InterruptFunctionHandler mInterruptFuncHandler;

	private final InterruptRequestHandler mIrqHandler;

	private Map<Integer, Procedure> mThreadProcedures = null;

	private final List<Statement> mAdditionalInitializations = new ArrayList<>();

	private final IsrLoopSearchVisitor mLoopSearchVisitor;

	public InterruptPostProcessor(final ILogger logger, final TranslationSettings settings,
			final ProcedureManager procedureManager, final CHandler chandler, final AuxVarInfoBuilder auxVarInfoBuilder,
			final ExpressionTranslation expressionTranslation, final InterruptFunctionHandler interruptFuncHandler,
			final InterruptRequestHandler irqHandler) {
		mLogger = logger;
		mProcedureManager = procedureManager;
		mCHandler = chandler;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mExpressionTranslation = expressionTranslation;
		mTranslationMode = settings.interruptTranslationMode();
		mEntryFunction = settings.getEntryFunction();
		mInterruptFuncHandler = interruptFuncHandler;
		mIrqHandler = irqHandler;
		mLoopSearchVisitor = new IsrLoopSearchVisitor(mInterruptFuncHandler.getIsrs());
	}

	@Override
	public List<Declaration> postProcess(final ILocation loc, final IASTNode hook,
			final List<Statement> additionalInitializations) {

		if (mTranslationMode == InterruptTranslationMode.NONE) {
			return List.of();
		}

		final ArrayList<Declaration> decl = new ArrayList<>();
		final var realization3 = mTranslationMode == InterruptTranslationMode.ONE_THREAD_PER_ISR_FORK_JOIN;

		// Get main procedure of program
		final Procedure mainProcedure;
		if (!mEntryFunction.equals(SFO.EMPTY) && mProcedureManager.hasProcedure(mEntryFunction)) {
			mainProcedure = mProcedureManager.getProcedureDeclaration(mEntryFunction);
		} else {
			// Abort interrupt post processing if there is no main function
			return List.of();
		}

		mLogger.info("Verify Interrupt-Driven Program with %d interrupt service routines",
				mInterruptFuncHandler.getIsrs().size());

		final var isrs = mInterruptFuncHandler.getIsrs();

		// Construct thread procedures for each ISR (stored for later use in fork/join)
		mThreadProcedures = constructThreadProcedures(isrs);
		final var threadProcedures = mThreadProcedures.values().stream()
				.filter(java.util.Objects::nonNull)
				.collect(Collectors.toList());
		decl.addAll(threadProcedures);

		// Add fork statements to the main procedure
		if (!realization3) {
			addForksToProcedure(mainProcedure, threadProcedures);
		}

		// Resolve masking functions to (irqNum, procedure) pairs, expanding AllInterrupts references
		final Map<Integer, Procedure> reqEnableFuncs = resolveMaskingFunctionProcedures(
				InterruptMaskingFunction.Operation.ENABLE);
		final Map<Integer, Procedure> reqDisableFuncs = resolveMaskingFunctionProcedures(
				InterruptMaskingFunction.Operation.DISABLE);

		// Add atomic block and variable assignment true to request enabled functions
		annotateRequestProcedures(reqEnableFuncs, isrs, true);

		// Add fork statements in request enable procedure instead of the main procedure
		if (realization3) {
			addForksToRequestEnable(reqEnableFuncs);
		}
		// Add atomic block and variable assignment false to request disabled functions
		annotateRequestProcedures(reqDisableFuncs, isrs, false);

		// Add join statements to request disable procedure
		if (realization3) {
			addJoinsToRequestDisable(reqDisableFuncs);
		}

		// Add interrupt enabled variable declarations (one per ISR)
		for (final var isr : isrs) {
			decl.add(constructEnabledDeclaration(getIrqNum(isr)));
		}

		// Add initialization statements (set all enabled variables to false)
		final var initLhs = isrs.stream()
				.map(isr -> constructEnabledLhs(getIrqNum(isr)))
				.collect(Collectors.toList());
		mAdditionalInitializations.add(constructAuxVarEnabledInitializations(initLhs));

		return decl;
	}

	private void addForksToProcedure(final Procedure mainProcedure, final List<Procedure> threadProcedures) {
		final List<Statement> newBlock = constructForkStatements(mainProcedure, threadProcedures, -1);
		final var body = mainProcedure.getBody();
		newBlock.addAll(Arrays.asList(body.getBlock()));
		body.setBlock(newBlock.toArray(new Statement[0]));
	}

	private void addForksToRequestEnableAll(final Procedure mainProcedure) {
		if (mainProcedure == null) {
			return;
		}
		final var statements = new ArrayList<Statement>();
		for (final var isr : mInterruptFuncHandler.getIsrs()) {
			final var irq = getIrqNum(isr);
			final var proc = mThreadProcedures.get(irq);
			if (proc == null) {
				continue;
			}
			final var fork = constructForkStatements(mainProcedure, List.of(proc), -irq);
			final var ifStmt = constructForkIfStatement(constructEnabledExpression(irq), fork, true);
			statements.add(ifStmt);
		}
		final var body = mainProcedure.getBody();
		statements.addAll(Arrays.asList(body.getBlock()));
		body.setBlock(statements.toArray(new Statement[0]));
	}

	private void addForksToRequestEnable(final Map<Integer, Procedure> intEnabledProcedures) {
		for (final Entry<Integer, Procedure> entry : intEnabledProcedures.entrySet()) {
			final var irq = entry.getKey();
			final var proc = entry.getValue();
			final var threadProc = mThreadProcedures.get(irq);
			if (threadProc == null) {
				continue;
			}

			final var thrNum = -irq;
			final List<Statement> fork = constructForkStatements(proc, List.of(threadProc), thrNum);

			final var newBlock = new ArrayList<>(List.of(constructForkIfStatement(constructEnabledExpression(irq), fork, true)));
			final var body = proc.getBody();
			newBlock.addAll(Arrays.asList(body.getBlock()));
			body.setBlock(newBlock.toArray(new Statement[0]));
		}
	}

	private void addJoinsToRequestDisable(final Map<Integer, Procedure> intDisabledProcedures) {
		for (final Entry<Integer, Procedure> entry : intDisabledProcedures.entrySet()) {
			final var irq = entry.getKey();
			final var proc = entry.getValue();
			if (!mThreadProcedures.containsKey(irq)) {
				continue;
			}
			final List<Statement> join = constructJoinStatement(proc, -irq);
			final var newBlock = new ArrayList<>(List.of(constructForkIfStatement(constructEnabledExpression(irq), join, false)));
			final var body = proc.getBody();
			newBlock.addAll(Arrays.asList(body.getBlock()));
			body.setBlock(newBlock.toArray(new Statement[0]));
		}
	}

	private List<Statement> constructForkStatements(final Procedure mainProcedure,
			final List<Procedure> threadProcedures, final Integer threadNum) {
		mProcedureManager.beginProcedureScope(mCHandler,
				mProcedureManager.getProcedureInfo(mainProcedure.getIdentifier()));
		assert threadNum <= 0;
		final var forkStatements = new ArrayList<Statement>();
		final String threadNumString = String.valueOf(threadNum);
		final var threadId = ExpressionFactory.createIntegerLiteral(mIgnoreLoc, threadNumString);
		for (final Procedure procedure : threadProcedures) {
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

	private Statement constructForkIfStatement(final Expression conditionExpr, final List<Statement> statements,
			final boolean negated) {
		Expression condition = conditionExpr;
		if (negated) {
			condition = ExpressionFactory.constructUnaryExpression(mIgnoreLoc,
					de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator.LOGICNEG, conditionExpr);
		}
		return StatementFactory.constructIfStatement(mIgnoreLoc, condition, statements);
	}

	private Statement constructAuxVarEnabledInitializations(final Collection<VariableLHS> leftHandSides) {
		final Expression assignment = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, false);
		final Expression[] assignments = new Expression[leftHandSides.size()];
		Arrays.fill(assignments, assignment);
		return StatementFactory.constructAssignmentStatement(mIgnoreLoc, leftHandSides.toArray(new LeftHandSide[0]),
				assignments);
	}

	private void annotateRequestProcedures(final Map<Integer, Procedure> intEnabledProcedures,
			final List<InterruptServiceFunction> isrs, final boolean enabled) {
		if (intEnabledProcedures == null) {
			return;
		}
		final String func = enabled ? " enable " : " disable ";
		for (final var isr : isrs) {
			final var irq = getIrqNum(isr);

			mLogger.info("Adding IRQ" + func + "function for ISR " + irq);

			final var intEnableProcedure = intEnabledProcedures.get(irq);
			if (intEnableProcedure == null) {
				mLogger.warn("There exists no IRQ" + func + "function for ISR " + irq);
				continue;
			}
			annotateAuxVarAssignment(intEnableProcedure, enabled, List.of(constructEnabledLhs(irq)));
		}
	}

	private Map<Integer, Procedure> resolveMaskingFunctionProcedures(final InterruptMaskingFunction.Operation op) {
		final var result = new HashMap<Integer, Procedure>();
		for (final var func : mInterruptFuncHandler.getFunctions(InterruptMaskingFunction.class)) {
			if (func.getOperation() != op) {
				continue;
			}
			final var irqRefs = func.getIrqReference().resolve(mIrqHandler);
			if (irqRefs == null) {
				continue;
			}
			for (final InterruptRequest irq : irqRefs) {
				result.putIfAbsent(irq.getNum(), func.getProcedure());
			}
		}
		return result;
	}

	private void annotateRequestAllProcedures(final Procedure intEnabledProcedure, final boolean enabled) {
		if (intEnabledProcedure == null) {
			return;
		}
		final var allLhs = mInterruptFuncHandler.getIsrs().stream()
				.map(isr -> constructEnabledLhs(getIrqNum(isr)))
				.collect(Collectors.toList());
		annotateAuxVarAssignment(intEnabledProcedure, enabled, allLhs);
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

	private Map<Integer, Procedure> constructThreadProcedures(final List<InterruptServiceFunction> isrs) {
		assert mTranslationMode != InterruptTranslationMode.NONE : "The chosen interrupt translation mode is NONE";
		final var result = new HashMap<Integer, Procedure>();
		final boolean oneThreadPerISR = mTranslationMode == InterruptTranslationMode.ONE_THREAD_PER_ISR
				|| mTranslationMode == InterruptTranslationMode.ONE_THREAD_PER_ISR_FORK_JOIN;
		if (oneThreadPerISR) {
			mLogger.info("Source-to-source translation of interrupt program with realization 1");
			for (final var isr : isrs) {
				result.put(getIrqNum(isr), constructOneThreadPerIsr(isr));
			}
		} else {
			mLogger.info("Source-to-source translation of interrupt program with realization 2");
			final var allThreadProc = constructOneThreadForAllIsrs(isrs);
			for (final var isr : isrs) {
				result.put(getIrqNum(isr), allThreadProc);
			}
		}
		return result;
	}

	// Realization 1
	private Procedure constructOneThreadPerIsr(final InterruptServiceFunction isr) {
		final int irqNum = getIrqNum(isr);
		final String procName = constructThreadName(irqNum, isr.getProcedure().getIdentifier());
		mLogger.info("Adding auxilliary ISR-Thread function " + procName + " for IRQ "
				+ isr.getIrqReference().getIrq().getName());
		final var declaration = new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0],
				new VarList[0], new Specification[0], null);
		mProcedureManager.beginCustomProcedure(mCHandler, mIgnoreLoc, procName, declaration);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final var whileStmt = constructIsrWhileLoop(isr);
		builder.addStatement(whileStmt);
		final var body = mProcedureManager.constructBody(mIgnoreLoc,
				builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
				builder.getStatements().toArray(new Statement[builder.getStatements().size()]), procName);
		mProcedureManager.endCustomProcedure(mCHandler, procName);
		return new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0], new VarList[0],
				null, body);
	}

	// Realization 2
	private Procedure constructOneThreadForAllIsrs(final List<InterruptServiceFunction> isrs) {
		final var procName = constructThreadName("all");
		mLogger.info("Adding auxilliary ISR-Thread function " + procName + " for all IRQs");
		final var declaration = new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0],
				new VarList[0], new Specification[0], null);
		mProcedureManager.beginCustomProcedure(mCHandler, mIgnoreLoc, procName, declaration);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final var nondetVarInfo = getHavocAuxVar(builder);
		final var whileStmt = constructAllIsrWhileLoop(isrs, nondetVarInfo);
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

	private Statement constructIsrWhileLoop(final InterruptServiceFunction isr) {
		final int irqNum = getIrqNum(isr);
		final var enabledExpr = constructEnabledExpression(irqNum);
		final var ifStmt = getIfStatement(isr, enabledExpr);
		final var block = getIsrBlock(ifStmt, isr);
		final var forkJoin = mTranslationMode == InterruptTranslationMode.ONE_THREAD_PER_ISR_FORK_JOIN;
		final var loopCondition = forkJoin ? enabledExpr : ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, loopCondition, new LoopInvariantSpecification[0], block);
	}

	private Statement constructAllIsrWhileLoop(final List<InterruptServiceFunction> isrs, final AuxVarInfo auxVarInfo) {
		final var atomicStatements = new ArrayList<Statement>();
		for (final var isr : isrs) {
			final var ifStatements = new ArrayList<Statement>();
			final var boolHavoc = getHavocBoolStatements(auxVarInfo);
			ifStatements.addAll(boolHavoc);
			final var enabledExpression = constructEnabledExpressionForRealization2(getIrqNum(isr), auxVarInfo);
			ifStatements.add(getIfStatement(isr, enabledExpression));
			final var block = getIsrBlock(ifStatements, isr);
			atomicStatements.addAll(block);
		}
		final var alwaysTrue = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, alwaysTrue, new LoopInvariantSpecification[0],
				atomicStatements.toArray(new Statement[0]));
	}

	private List<Statement> getIsrBlock(final List<Statement> ifStatements, final InterruptServiceFunction isr) {
		if (ADD_ISR_LABELS && mLoopSearchVisitor.containsLoop(isr)) {
			return ifStatements;
		}
		return List.of(StatementFactory.constructAtomicStatement(mIgnoreLoc, ifStatements));
	}

	private Statement[] getIsrBlock(final Statement ifStatement, final InterruptServiceFunction isr) {
		if (ADD_ISR_LABELS && mLoopSearchVisitor.containsLoop(isr)) {
			return new Statement[] { ifStatement };
		}
		return new Statement[] { StatementFactory.constructAtomicStatement(mIgnoreLoc, List.of(ifStatement)) };
	}

	private Statement getIfStatement(final InterruptServiceFunction isr, final Expression enabledExpr) {
		final var interruptAnnotation = new InterruptAnnotation(ISRLocation.ENTRY, isr);
		final var then = StatementFactory.constructCallStatement(mIgnoreLoc, false, new VariableLHS[0],
				isr.getProcedure().getIdentifier(), new Expression[0]);
		if (ADD_ISR_LABELS && mLoopSearchVisitor.containsLoop(isr)) {
			mLogger.info("Add interrupt labels to call of function: " + isr.getProcedure().getIdentifier());
			final var ifStmt = StatementFactory.constructIfStatement(mIgnoreLoc, enabledExpr,
					labelIsrStatement(then, isr), new Statement[0]);
			// TODO: Handle annotation for contains case
			interruptAnnotation.annotate(ifStmt);
			return ifStmt;
		}
		return StatementFactory.constructIfStatement(mIgnoreLoc, enabledExpr, new Statement[] { then },
				new Statement[0]);
	}

	private Statement[] labelIsrStatement(final Statement isrStatement, final InterruptServiceFunction isr) {
		final String irqNum = Integer.toString(isr.getIrqReference().getIrq().getNum());
		final var labelName = "~isr" + irqNum;
		final var isrNumAttribute = new NamedAttribute(mIgnoreLoc, irqNum, new Expression[0]);
		final var isrAttribute = new NamedAttribute(mIgnoreLoc, "isr_label", new Expression[0]);
		final var entryAttribute = new NamedAttribute(mIgnoreLoc, "entry", new Expression[0]);
		final var exitAttribute = new NamedAttribute(mIgnoreLoc, "exit", new Expression[0]);
		final var entryLabel = new Label(mIgnoreLoc, labelName + "Entry",
				new NamedAttribute[] { isrAttribute, entryAttribute, isrNumAttribute });
		final var exitLabel = new Label(mIgnoreLoc, labelName + "Exit",
				new NamedAttribute[] { isrAttribute, exitAttribute, isrNumAttribute });
		return new Statement[] { entryLabel, isrStatement, exitLabel };
	}

	private static String constructThreadName(final String identifier) {
		return "#isr_" + identifier + "_thread";
	}

	private static String constructThreadName(final int irqNum, final String procIdentifier) {
		return "#isr_" + irqNum + "_" + procIdentifier + "_thread";
	}

	private static int getIrqNum(final InterruptServiceFunction isr) {
		return isr.getIrqReference().getIrq().getNum();
	}

	private static String constructEnabledVarName(final int irqNum) {
		return "#isr_" + irqNum + "_enabled";
	}

	private Expression constructEnabledExpression(final int irqNum) {
		return ExpressionFactory.constructIdentifierExpression(mIgnoreLoc, BoogieType.TYPE_BOOL,
				constructEnabledVarName(irqNum), DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	private VariableLHS constructEnabledLhs(final int irqNum) {
		return ExpressionFactory.constructVariableLHS(mIgnoreLoc, BoogieType.TYPE_BOOL,
				constructEnabledVarName(irqNum), DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	private VariableDeclaration constructEnabledDeclaration(final int irqNum) {
		final var varName = constructEnabledVarName(irqNum);
		final var astType = new PrimitiveType(mIgnoreLoc, "bool");
		return new VariableDeclaration(mIgnoreLoc, new Attribute[0],
				new VarList[] { new VarList(mIgnoreLoc, new String[] { varName }, astType) });
	}

	private Expression constructEnabledExpressionForRealization2(final int irqNum, final AuxVarInfo auxVarInfo) {
		final CPrimitive cType = new CPrimitive(CPrimitives.BOOL);
		final Expression isOne = ExpressionFactory.newBinaryExpression(mIgnoreLoc, Operator.COMPEQ, auxVarInfo.getExp(),
				mExpressionTranslation.constructLiteralForIntegerType(mIgnoreLoc, cType, BigInteger.ONE));
		return ExpressionFactory.and(mIgnoreLoc, List.of(constructEnabledExpression(irqNum), isOne));
	}

	public List<Statement> getAdditionalInitializations() {
		return mAdditionalInitializations;
	}

	private static class IsrLoopSearchVisitor {

		private final Map<InterruptServiceFunction, Boolean> mContainsLoop;

		private IsrLoopSearchVisitor(final List<InterruptServiceFunction> isrs) {
			mContainsLoop = visitIsrs(isrs);
		}

		private Map<InterruptServiceFunction, Boolean> visitIsrs(final List<InterruptServiceFunction> isrs) {
			final var containsLoopMap = new HashMap<InterruptServiceFunction, Boolean>();
			for (final InterruptServiceFunction isr : isrs) {
				final boolean containsLoop = visitProc(isr.getProcedure());
				containsLoopMap.put(isr, containsLoop);
			}
			return containsLoopMap;
		}

		private boolean visitProc(final Procedure proc) {
			return visitBody(proc.getBody());
		}

		private boolean visitBody(final Body body) {
			return visitBlock(body.getBlock());
		}

		private boolean visitBlock(final Statement[] statements) {
			for (final Statement statement : statements) {
				if (visitStatement(statement)) {
					return true;
				}
			}
			return false;
		}

		private boolean visitStatement(final Statement statement) {
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

		private boolean containsLoop(final InterruptServiceFunction isr) {
			final boolean contains = mContainsLoop.get(isr);
			return contains;
		}
	}
}
