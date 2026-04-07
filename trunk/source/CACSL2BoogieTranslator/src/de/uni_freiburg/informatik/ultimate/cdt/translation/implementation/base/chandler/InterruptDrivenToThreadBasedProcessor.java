/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
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

public class InterruptDrivenToThreadBasedProcessor implements IPostProcessor {

	private final ILogger mLogger;

	private final FlatSymbolTable mSymboltable;

	private final ProcedureManager mProcedureManager;

	private final CHandler mCHandler;

	private final TranslationSettings mSettings;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final ExpressionTranslation mExpressionTranslation;

	private final ILocation mIgnoreLoc = LocationFactory.createIgnoreCLocation();

	private final InterruptTranslationMode mTranslationMode;

	private final InterruptServiceRoutines mISR;

	private Map<Integer, IdentifierExpression> mAuxVarExpressions = null;

	private final List<Statement> mAdditionalInitializations = new ArrayList<>();

	public InterruptDrivenToThreadBasedProcessor(final ILogger logger, final FlatSymbolTable symbolTable,
			final TranslationSettings settings, final ProcedureManager procedureManager, final CHandler chandler,
			final AuxVarInfoBuilder auxVarInfoBuilder, final ExpressionTranslation expressionTranslation,
			final InterruptTranslationMode translationMode, final InterruptServiceRoutines isrs) {
		mLogger = logger;
		mSymboltable = symbolTable;
		mSettings = settings;
		mProcedureManager = procedureManager;
		mCHandler = chandler;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mExpressionTranslation = expressionTranslation;
		mTranslationMode = translationMode;
		mISR = isrs;
	}

	@Override
	public List<Declaration> postProcess(final ILocation loc, final IASTNode hook,
			final List<Statement> additionalInitializations) {
		final ArrayList<Declaration> decl = new ArrayList<>();

		// Get the ghost variables that signal whether an ISR is enabled
		mAuxVarExpressions = constructAuxVarExpressions(mISR.getISRMap().keySet());

		// Add thread gpio procedures
		final var threadGpioProcedures = constructThreadGpioProc();
		decl.addAll(threadGpioProcedures);

		// Add fork statements to the main procedure
		addForksToProcedure(mISR.getMainProcedure(), threadGpioProcedures);

		// Add atomic block and variable assignment to request enabled functions
		final var lhsMap = getVariableLHSs();
		annotateRequestEnableProcedures(lhsMap);

		// Add interrupt enabled variable declarations
		decl.addAll(constructAuxVarEnableDeclarations());

		mAdditionalInitializations.add(constructAuxVarEnabledInitializations(lhsMap.values()));

		return decl;
	}

	private void addForksToProcedure(final Procedure mainProcedure, final List<Procedure> threadGpioProcedures) {
		final List<Statement> newBlock = constructForkStatements(mainProcedure, threadGpioProcedures);
		final var body = mainProcedure.getBody();
		newBlock.addAll(Arrays.asList(body.getBlock()));
		body.setBlock(newBlock.toArray(new Statement[0]));
	}

	private List<Statement> constructForkStatements(final Procedure mainProcedure,
			final List<Procedure> threadGpioProcedures) {
		mProcedureManager.beginProcedureScope(mCHandler,
				mProcedureManager.getProcedureInfo(mainProcedure.getIdentifier()));
		final var forkStatements = new ArrayList<Statement>();
		for (final Procedure procedure : threadGpioProcedures) {
			final var fs =
					new ForkStatement(mIgnoreLoc, new Expression[0], procedure.getIdentifier(), new Expression[0]);
			forkStatements.add(fs);
			mProcedureManager.registerForkStatement(fs);
		}
		mProcedureManager.endProcedureScope(mCHandler);
		return forkStatements;
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
			final var id = "gpio_int" + irq + "_enabled";
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

	private void annotateRequestEnableProcedures(final Map<Integer, VariableLHS> lhsMap) {
		final var intEnabledProcedures = mISR.getRequestEnable();
		for (final Entry<Integer, VariableLHS> entry : lhsMap.entrySet()) {
			final var irq = entry.getKey();
			final var lhs = entry.getValue();
			final var intEnableProcedure = intEnabledProcedures.get(irq);
			assert intEnableProcedure != null : "There exists no request enable procedure for IRQ: " + irq;
			annotateRequestEnableProcedure(intEnableProcedure, lhs);
		}
	}

	private void annotateRequestEnableProcedure(final Procedure intEnableProcedure, final VariableLHS intEnabledLhs) {
		mProcedureManager.beginProcedureScope(mCHandler,
				mProcedureManager.getProcedureInfo(intEnableProcedure.getIdentifier()));
		final var body = intEnableProcedure.getBody();
		final var block = body.getBlock();
		final var assignment = StatementFactory.constructSingleAssignmentStatement(mIgnoreLoc, intEnabledLhs,
				ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true));
		final var newBlock = new ArrayList<>(Arrays.asList(block));
		newBlock.add(assignment);
		final var atomic = StatementFactory.constructAtomicStatement(mIgnoreLoc, newBlock);
		final var newBody = mProcedureManager.constructBody(mIgnoreLoc, new VariableDeclaration[0],
				new Statement[] { atomic }, intEnableProcedure.getIdentifier());
		body.setBlock(newBody.getBlock());
		mProcedureManager.endProcedureScope(mCHandler);
	}

	private void addIntEnabledToSpecification(final Procedure intEnableSpec, final VariableLHS intEnabledLhs) {
		mProcedureManager.beginProcedureScope(mCHandler,
				mProcedureManager.getProcedureInfo(intEnableSpec.getIdentifier()));
		final var modifiesSpec = new ModifiesSpecification(mIgnoreLoc, false, new VariableLHS[] { intEnabledLhs });
		mProcedureManager.addSpecificationsToCurrentProcedure(List.of(modifiesSpec));
		mProcedureManager.endProcedureScope(mCHandler);

	}

	private ArrayList<Procedure> constructThreadGpioProc() {
		assert mTranslationMode != InterruptTranslationMode.NONE : "The chosen interrupt translation mode is NONE";
		final var procedures = new ArrayList<Procedure>();
		if (mTranslationMode == InterruptTranslationMode.REALIZATION_1) {
			final var isrGpios = mISR.getISRMap().entrySet();
			for (final Entry<Integer, Procedure> entry : isrGpios) {
				final var irq = entry.getKey();
				final var isr = entry.getValue();
				final var procId = isr.getIdentifier();
				final var idExpression = mAuxVarExpressions.get(irq);
				assert idExpression != null : "There exists no identifier expression for the IRQ: " + irq;
				procedures.add(constructOneInterruptThreadGpioProc(procId, idExpression, irq));
			}
		} else {
			procedures.add(constructAllInterruptsThreadGpioProc());
		}
		return procedures;
	}

	// Realization 1
	private Procedure constructOneInterruptThreadGpioProc(final String identifier,
			final IdentifierExpression threadEnabledId, final Integer irq) {
		final var procName = constructThreadGpioID(irq);
		final var declaration = new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0],
				new VarList[0], new Specification[0], null);
		mProcedureManager.beginCustomProcedure(mCHandler, mIgnoreLoc, procName, declaration);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final var whileStmt = constructIsrWhileLoop(identifier, threadEnabledId);
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
		final var procName = constructThreadGpioID(0);
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

	private Statement constructIsrWhileLoop(final String identifier, final IdentifierExpression threadEnabledId) {
		// TODO: Maybe this needs to be registered in ProcedureManager
		final var enabledExpr = threadEnabledId;
		final var ifStmt = getIfStatement(identifier, threadEnabledId, enabledExpr);
		final var atomic = StatementFactory.constructAtomicStatement(mIgnoreLoc, List.of(ifStmt));
		final var alwaysTrue = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, alwaysTrue, new LoopInvariantSpecification[0],
				new Statement[] { atomic });
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
			ifStatements.add(getIfStatement(identifier, threadEnabledId, enabledExpression));
			final var atomic = StatementFactory.constructAtomicStatement(mIgnoreLoc, ifStatements);
			atomicStatements.add(atomic);
		}
		final var alwaysTrue = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, alwaysTrue, new LoopInvariantSpecification[0],
				atomicStatements.toArray(new Statement[0]));
	}

	private Statement getIfStatement(final String identifier, final IdentifierExpression threadEnabledId,
			final Expression enabledExpr) {
		final var then = StatementFactory.constructCallStatement(mIgnoreLoc, false, new VariableLHS[0], identifier,
				new Expression[0]);
		return StatementFactory.constructIfStatement(mIgnoreLoc, enabledExpr, new Statement[] { then },
				new Statement[0]);
	}

	private Expression getEnabledExpression(final IdentifierExpression threadEnabledId, final AuxVarInfo auxVarInfo) {
		final CPrimitive cType = new CPrimitive(CPrimitives.BOOL);
		final Expression isOne = ExpressionFactory.newBinaryExpression(mIgnoreLoc, Operator.COMPEQ, auxVarInfo.getExp(),
				mExpressionTranslation.constructLiteralForIntegerType(mIgnoreLoc, cType, BigInteger.ONE));
		return ExpressionFactory.and(mIgnoreLoc, List.of(threadEnabledId, isOne));
	}

	private String constructThreadGpioID(final Integer irq) {
		return "thr_gpio" + irq;
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
}
