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
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptServiceRoutines;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptTranslationMode;
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

	private final ILocation mIgnoreLoc = LocationFactory.createIgnoreCLocation();

	private final InterruptTranslationMode mTranslationMode;

	private final InterruptServiceRoutines mISR;

	private Map<Integer, IdentifierExpression> mIdExpressions = null;

	private final List<Statement> mAdditionalInitializations = new ArrayList<>();

	public InterruptDrivenToThreadBasedProcessor(final ILogger logger, final FlatSymbolTable symbolTable,
			final TranslationSettings settings, final ProcedureManager procedureManager, final CHandler chandler,
			final InterruptTranslationMode translationMode, final InterruptServiceRoutines isrs) {
		mLogger = logger;
		mSymboltable = symbolTable;
		mSettings = settings;
		mProcedureManager = procedureManager;
		mCHandler = chandler;
		mTranslationMode = translationMode;
		mISR = isrs;
	}

	@Override
	public List<Declaration> postProcess(final ILocation loc, final IASTNode hook,
			final List<Statement> additionalInitializations) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		mIdExpressions = constructIntEnabledExpressions(mISR.getISRMap().keySet());

		// Add interrupt enabled variable declarations
		decl.addAll(constructIntEnableDeclarations());

		// Add thread gpio procedures
		final var threadGpioProcedures = constructThreadGpioProc();
		decl.addAll(threadGpioProcedures);

		// Add fork statements to the main procedure
		addForksToProcedure(mISR.getMainProcedure(), threadGpioProcedures);

		// Add atomic block and variable assignment to request enabled functions
		final var lhsMap = getVariableLHSs();
		modifyIntEnableProcedures(lhsMap);

		mAdditionalInitializations.add(constructIntEnabledInitializations(lhsMap.values()));

		return decl;
	}

	private void addForksToProcedure(final Procedure mainProcedure, final List<Procedure> threadGpioProcedures) {
		final List<Statement> newBlock = constructForkStatements(threadGpioProcedures);
		final var body = mainProcedure.getBody();
		newBlock.addAll(Arrays.asList(body.getBlock()));
		body.setBlock(newBlock.toArray(new Statement[0]));
	}

	private List<Statement> constructForkStatements(final List<Procedure> threadGpioProcedures) {
		final var forkStatements = new ArrayList<Statement>();
		for (final Procedure procedure : threadGpioProcedures) {
			final var fs =
					new ForkStatement(mIgnoreLoc, new Expression[0], procedure.getIdentifier(), new Expression[0]);
			forkStatements.add(fs);
		}
		return forkStatements;
	}

	private Set<Declaration> constructIntEnableDeclarations() {
		final var declarations = new HashSet<Declaration>();
		final var astType = new NamedType(mIgnoreLoc, BoogieType.TYPE_BOOL, "bool", new ASTType[0]);
		for (final IdentifierExpression identifierExpression : mIdExpressions.values()) {
			final var decl = new VariableDeclaration(mIgnoreLoc, new Attribute[0], new VarList[] {
					new VarList(mIgnoreLoc, new String[] { identifierExpression.getIdentifier() }, astType) });
			declarations.add(decl);
		}
		return declarations;
	}

	private Map<Integer, IdentifierExpression> constructIntEnabledExpressions(final Collection<Integer> identifiers) {
		final var idExpressions = new HashMap<Integer, IdentifierExpression>();
		for (final Integer irq : identifiers) {
			final var id = "gpio_int" + irq + "_enabled";
			final var enabledExpr = ExpressionFactory.constructIdentifierExpression(mIgnoreLoc, BoogieType.TYPE_BOOL,
					id, DeclarationInformation.DECLARATIONINFO_GLOBAL);
			idExpressions.put(irq, enabledExpr);
		}
		return idExpressions;
	}

	private Statement constructIntEnabledInitializations(final Collection<VariableLHS> leftHandSides) {
		final Expression assignment = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, false);
		final Expression[] assignments = new Expression[leftHandSides.size()];
		Arrays.fill(assignments, assignment);
		return StatementFactory.constructAssignmentStatement(mIgnoreLoc, leftHandSides.toArray(new LeftHandSide[0]),
				assignments);
	}

	private void modifyIntEnableProcedures(final Map<Integer, VariableLHS> lhsMap) {
		final var intEnabledProcedures = mISR.getRequestEnable();
		for (final Entry<Integer, VariableLHS> entry : lhsMap.entrySet()) {
			final var irq = entry.getKey();
			final var lhs = entry.getValue();
			final var intEnableProcedure = intEnabledProcedures.get(irq);
			assert intEnableProcedure != null : "There exists no request enable procedure for IRQ: " + irq;
			modifyIntEnableProcedure(intEnableProcedure, lhs);
			addIntEnabledToSpecification(intEnableProcedure, lhs);
		}
	}

	private void modifyIntEnableProcedure(final Procedure intEnableProcedure, final VariableLHS intEnabledLhs) {
		final var body = intEnableProcedure.getBody();
		final var block = body.getBlock();
		final var assignment = StatementFactory.constructSingleAssignmentStatement(mIgnoreLoc, intEnabledLhs,
				ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true));
		final var newBlock = Arrays.asList(block);
		newBlock.add(assignment);
		final var atomic = StatementFactory.constructAtomicStatement(mIgnoreLoc, newBlock);
		body.setBlock(new Statement[] { atomic });
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
				final var idExpression = mIdExpressions.get(irq);
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
				new VarList[0], null, null);
		mProcedureManager.beginCustomProcedure(mCHandler, mIgnoreLoc, SFO.INIT, declaration);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final var whileStmt = constructIsrWhileLoop(identifier, threadEnabledId);
		builder.addStatement(whileStmt);
		final var body = mProcedureManager.constructBody(mIgnoreLoc,
				builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
				builder.getStatements().toArray(new Statement[builder.getStatements().size()]), procName);
		mProcedureManager.endCustomProcedure(mCHandler, SFO.INIT);
		return new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0], new VarList[0],
				null, body);
	}

	// Realization 2

	private Procedure constructAllInterruptsThreadGpioProc() {
		final var procName = constructThreadGpioID(0);
		final var declaration = new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0],
				new VarList[0], null, null);
		mProcedureManager.beginCustomProcedure(mCHandler, mIgnoreLoc, SFO.INIT, declaration);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final var whileStmt = constructAllIsrWhileLoop();
		builder.addStatement(whileStmt);
		final var body = mProcedureManager.constructBody(mIgnoreLoc,
				builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
				builder.getStatements().toArray(new Statement[builder.getStatements().size()]), procName);
		mProcedureManager.endCustomProcedure(mCHandler, SFO.INIT);
		return new Procedure(mIgnoreLoc, new Attribute[0], procName, new String[0], new VarList[0], new VarList[0],
				null, body);
	}

	private Statement constructIsrWhileLoop(final String identifier, final IdentifierExpression threadEnabledId) {
		// TODO: Maybe this needs to be registered in ProcedureManager
		final var ifStmt = getIfStatement(identifier, threadEnabledId, false);
		final var atomic = StatementFactory.constructAtomicStatement(mIgnoreLoc, List.of(ifStmt));
		final var alwaysTrue = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, alwaysTrue, new LoopInvariantSpecification[0],
				new Statement[] { atomic });
	}

	private Statement constructAllIsrWhileLoop() {
		final var ifStatements = new ArrayList<Statement>();
		for (final Entry<Integer, Procedure> entry : mISR.getISRMap().entrySet()) {
			final var irq = entry.getKey();
			final var identifier = entry.getValue().getIdentifier();
			final var threadEnabledId = mIdExpressions.get(irq);
			assert threadEnabledId != null : "There exists no IdentifierExpression of ISR with IRQ: " + irq;
			ifStatements.add(getIfStatement(identifier, threadEnabledId, true));
		}
		final var atomic = StatementFactory.constructAtomicStatement(mIgnoreLoc, ifStatements);
		final var alwaysTrue = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, alwaysTrue, new LoopInvariantSpecification[0],
				new Statement[] { atomic });
	}

	private Statement getIfStatement(final String identifier, final IdentifierExpression threadEnabledId,
			final boolean andWildcard) {
		final var then = StatementFactory.constructCallStatement(mIgnoreLoc, false, new VariableLHS[0], identifier,
				new Expression[0]);
		final var enabledExpr = getEnabledExpression(threadEnabledId, andWildcard);
		return StatementFactory.constructIfStatement(mIgnoreLoc, enabledExpr, new Statement[] { then }, null);
	}

	private Expression getEnabledExpression(final IdentifierExpression threadEnabledId, final boolean andWildcard) {
		if (andWildcard) {
			return threadEnabledId;
		}
		final var wildCard = ExpressionFactory.constructBooleanWildCardExpression(mIgnoreLoc);
		return ExpressionFactory.newBinaryExpression(mIgnoreLoc,
				de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator.LOGICAND, threadEnabledId,
				wildCard);
	}

	private String constructThreadGpioID(final Integer irq) {
		return "thr_gpio" + irq;
	}

	private Map<Integer, VariableLHS> getVariableLHSs() {
		return mIdExpressions.entrySet().stream().collect(
				Collectors.toMap(Entry::getKey, e -> new VariableLHS(mIgnoreLoc, e.getValue().getIdentifier())));
	}

	public List<Statement> getAdditionalInitializations() {
		return mAdditionalInitializations;
	}
}
