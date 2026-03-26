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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.IPostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.ThreadIdManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class InterruptDrivenToThreadBasedProcessor implements IPostProcessor {

	private final ILogger mLogger;

	private final FlatSymbolTable mSymboltable;

	private final MemoryHandler mMemoryHandler;

	private final ProcedureManager mProcedureManager;

	private final CHandler mCHandler;

	private final TypeSizes mTypeSize;

	private final TranslationSettings mSettings;

	private final FunctionHandler mFunctionhandler;

	private final ILocation mIgnoreLoc = LocationFactory.createIgnoreCLocation();

	private final ThreadIdManager mThreadIdManager;

	public InterruptDrivenToThreadBasedProcessor(final ILogger logger,
			final ExpressionTranslation expressionTranslation, final ITypeHandler typeHandler,
			final AuxVarInfoBuilder auxVarInfoBuilder, final TypeSizes typeSizes, final FlatSymbolTable symbolTable,
			final TranslationSettings settings, final ProcedureManager procedureManager,
			final MemoryHandler memoryHandler, final FunctionHandler functionhandler, final CHandler chandler,
			final ExpressionResultTransformer expressionResultTransformer) {
		mLogger = logger;
		mTypeSize = typeSizes;
		mSymboltable = symbolTable;
		mSettings = settings;
		mProcedureManager = procedureManager;
		mMemoryHandler = memoryHandler;
		mFunctionhandler = functionhandler;
		mCHandler = chandler;
		mThreadIdManager = new ThreadIdManager(auxVarInfoBuilder, expressionResultTransformer, expressionTranslation,
				mMemoryHandler, typeHandler, mTypeSize, null /* TODO */, symbolTable);
	}

	@Override
	public List<Declaration> postProcess(final ILocation loc, final IASTNode hook,
			final List<Statement> additionalInitializations) {
		// TODO Auto-generated method stub
		return null;
	}

	private void addForksToProcedure(final Procedure mainProcedure, final Set<Procedure> threadGpioProcedures) {
		final List<Statement> newBlock = constructForkStatements(threadGpioProcedures);
		final var body = mainProcedure.getBody();
		newBlock.addAll(Arrays.asList(body.getBlock()));
		body.setBlock(newBlock.toArray(new Statement[0]));
	}

	private List<Statement> constructForkStatements(final Set<Procedure> threadGpioProcedures) {
		final var forkStatements = new ArrayList<Statement>();
		for (final Procedure procedure : threadGpioProcedures) {
			final var fs =
					new ForkStatement(mIgnoreLoc, new Expression[0], procedure.getIdentifier(), new Expression[0]);
			forkStatements.add(fs);
		}
		return forkStatements;
	}

	private Set<Declaration> constructIntEnableDeclarations(final List<IdentifierExpression> identifierExpressions) {
		final var declarations = new HashSet<Declaration>();
		final var astType = new NamedType(mIgnoreLoc, BoogieType.TYPE_BOOL, "bool", new ASTType[0]);
		for (final IdentifierExpression identifierExpression : identifierExpressions) {
			final var decl = new VariableDeclaration(mIgnoreLoc, new Attribute[0], new VarList[] {
					new VarList(mIgnoreLoc, new String[] { identifierExpression.getIdentifier() }, astType) });
			declarations.add(decl);
		}
		return declarations;
	}

	private Map<Integer, IdentifierExpression> constructIntEnabledExpressions(final List<Integer> identifiers) {
		final var idExpressions = new HashMap<Integer, IdentifierExpression>();
		for (final Integer irq : identifiers) {
			final var id = "gpio_int" + irq + "_enabled";
			final var enabledExpr = ExpressionFactory.constructIdentifierExpression(mIgnoreLoc, BoogieType.TYPE_BOOL,
					id, DeclarationInformation.DECLARATIONINFO_GLOBAL);
			idExpressions.put(irq, enabledExpr);
		}
		return idExpressions;
	}

	private Statement constructIntEnabledInitializations(final List<VariableLHS> leftHandSides) {
		final Expression assignment = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, false);
		final Expression[] assignments = new Expression[leftHandSides.size()];
		Arrays.fill(assignments, assignment);
		return StatementFactory.constructAssignmentStatement(mIgnoreLoc, leftHandSides.toArray(new LeftHandSide[0]),
				assignments);
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

	private Procedure addIntEnabledToSpecification(final Procedure intEnableSpec, final VariableLHS intEnabledLhs) {
		// Adjust modify specification
		final var oldSpec = intEnableSpec.getSpecification();
		final var modifiesSpec = new ModifiesSpecification(mIgnoreLoc, false, new VariableLHS[] { intEnabledLhs });
		final var newSpec = Arrays.copyOf(oldSpec, oldSpec.length + 1);
		newSpec[oldSpec.length] = modifiesSpec;
		return new Procedure(intEnableSpec.getLoc(), intEnableSpec.getAttributes(), intEnableSpec.getIdentifier(),
				intEnableSpec.getTypeParams(), intEnableSpec.getInParams(), intEnableSpec.getOutParams(), newSpec,
				intEnableSpec.getBody());
	}

	private Procedure constructThreadGpioProc(final String identifier, final IdentifierExpression threadEnabledId,
			final Integer irq) {
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

	private Statement constructIsrWhileLoop(final String identifier, final IdentifierExpression threadEnabledId) {
		// TODO: Maybe this needs to be registered in ProcedureManager
		final var then = StatementFactory.constructCallStatement(mIgnoreLoc, false, new VariableLHS[0], identifier,
				new Expression[0]);
		final var enabledExpr =
				ExpressionFactory.constructUnaryExpression(mIgnoreLoc, Operator.LOGICNEG, threadEnabledId);
		final var ifStmt =
				StatementFactory.constructIfStatement(mIgnoreLoc, enabledExpr, new Statement[] { then }, null);
		final var atomic = StatementFactory.constructAtomicStatement(mIgnoreLoc, List.of(ifStmt));
		final var alwaysTrue = ExpressionFactory.createBooleanLiteral(mIgnoreLoc, true);
		return new WhileStatement(mIgnoreLoc, alwaysTrue, new LoopInvariantSpecification[0],
				new Statement[] { atomic });
	}

	private String constructThreadGpioID(final Integer irq) {
		return "thr_gpio" + irq;
	}
}
