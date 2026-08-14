/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVariableCollector;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.civlizer.ProgramAndProof.GhostUpdateLocation;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration.Linearity;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Transforms Boogie procedure bodies into their Civl thread template bodies.
 *
 * <p>
 * This transformer rewrites statements of a procedure in order to introduce the statement representation in Civl and
 * proof.
 * </p>
 *
 * <p>
 * In particular, the transformation:
 * <ul>
 * <li>Introduces calls to generated atomic actions for statements accessing shared state.</li>
 * <li>Inserts yield invariant.</li>
 * <li>Rewrites thread-management statements such as {@code fork} and {@code join} into their Civl concurrency-flow
 * operation calls.</li>
 * <li>Injects ghost-variable updates generated from proof annotations.</li>
 * </ul>
 * </p>
 *
 * <p>
 * The transformation is performed procedure by procedure while maintaining statement numbering used to reference
 * generated yield procedures and atomic actions.
 * </p>
 *
 * @author Gabriel Tréca (gabriel.treca@polytechnique.edu)
 * @author Dominik Klumpp (klumpp@lix.polytechnique.fr)
 */
final class BodyTransformer extends BoogieTransformer {
	private final ILogger mLogger;
	private final Translator mTranslator;
	private final String mProcedureName;

	private final IdentifierExpression[] mCurrentTids;
	private final Set<Tid> mTidNeedsLinearity;
	private int mAtomicStatementCounter;

	private VariableDeclaration mConditionVariable;

	private final Body mResult;

	/**
	 * Creates a new body transformer.
	 */
	BodyTransformer(final IUltimateServiceProvider services, final Translator translator, final String procedureName,
			final Body body) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mTranslator = translator;
		mProcedureName = procedureName;

		final int size = mTranslator.getProgramAndProof().getTemplateVisitor().getAllTidMap()
				.getOrDefault(mProcedureName, Collections.emptyList()).size()
				+ (mProcedureName.equals(BoogieUtils.START_PROCEDURE) ? 1 : 0);

		final IdentifierExpression[] tids = new IdentifierExpression[size];
		int i = 0;
		if (mProcedureName.equals(BoogieUtils.START_PROCEDURE)) {
			tids[i] = new IdentifierExpression(null, BoogieType.createPlaceholderType(0), "start_tid",
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
			i++;
		}
		for (final Tid tid : mTranslator.getProgramAndProof().getTemplateVisitor().getAllTidMap()
				.getOrDefault(mProcedureName, Collections.emptyList())) {
			tids[i] = new IdentifierExpression(null, BoogieType.createPlaceholderType(0), tid.toString(),
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
			i++;
		}

		mCurrentTids = tids;
		// TODO maybe use mAllTidMap
		mTidNeedsLinearity = new HashSet<>(mTranslator.getProgramAndProof().getTemplateVisitor().getTids());

		mResult = processBody(body);
	}

	public Body getResult() {
		return mResult;
	}

	@Override
	protected Body processBody(final Body body) {
		final var newBody = super.processBody(body);

		// insert additional statements
		final var newStatements = new ArrayList<>(Arrays.asList(newBody.getBlock()));

		final Expression annotation =
				mTranslator.getProgramAndProof().getTemplateVisitor().getExitAnnotationMap().get(mProcedureName);
		final var yieldInvariant =
				mTranslator.addYieldInvariant(mProcedureName, mAtomicStatementCounter, annotation, mTidNeedsLinearity);
		newStatements.add(mTranslator.callYieldInvariant(yieldInvariant, mCurrentTids, annotation));

		if (mProcedureName != BoogieUtils.START_PROCEDURE) {
			newStatements.add(new CallStatement(null, new NamedAttribute[0], false, new VariableLHS[0], "terminate",
					mCurrentTids));
		}

		// insert additional local variables, if needed
		final var newLocals = new ArrayList<>(Arrays.asList(newBody.getLocalVars()));
		if (mConditionVariable != null) {
			newLocals.add(mConditionVariable);
		}

		return new Body(newBody.getLoc(), newLocals.toArray(VariableDeclaration[]::new),
				newStatements.toArray(Statement[]::new));
	}

	/**
	 * Rewrites the statements of the current procedure.
	 *
	 * <p>
	 * Depending on the accessed variables and the statement kind, statements may be:
	 * <ul>
	 * <li>left unchanged,</li>
	 * <li>annotated with Civl layers,</li>
	 * <li>replaced by calls to generated atomic actions,</li>
	 * <li>rewritten into fork/join operations,</li>
	 * <li>followed by calls to generated yield invariants.</li>
	 * </ul>
	 * </p>
	 *
	 * @param statements
	 *            the statements to transform
	 * @return the transformed statements
	 */
	@Override
	protected Statement[] processStatements(final Statement[] statements) {
		final List<Statement> newStatements = new ArrayList<>();

		final var inParams = new ArrayList<ParameterDeclaration>();
		if (BoogieUtils.START_PROCEDURE.equals(mProcedureName)) {
			inParams.add(new ParameterDeclaration("start_tid", Translator.makeOne(mTranslator.getStartTidType()),
					Linearity.INOUT));
		}
		for (final Tid tid : mTranslator.getProgramAndProof().getTemplateVisitor().getAllTidMap()
				.getOrDefault(mProcedureName, Collections.emptyList())) {
			inParams.add(new ParameterDeclaration(tid.toString(), Translator.makeOne(mTranslator.getTidType()),
					Linearity.IN));
		}

		final Map<ILocation, Expression> annotationMap = mTranslator.getProgramAndProof().getAnnotationMap();
		final var ghostUpdateMap = mTranslator.getProgramAndProof().getGhostUpdateMap();

		for (final Statement statement : statements) {
			mAtomicStatementCounter += 1;

			final var annotation = annotationMap.get(statement.getLoc());
			final var yieldInvariant = mTranslator.addYieldInvariant(mProcedureName, mAtomicStatementCounter,
					annotation, mTidNeedsLinearity);
			final var annotationCheck = mTranslator.callYieldInvariant(yieldInvariant, mCurrentTids, annotation);

			final List<CallStatement> positiveGhostUpdates = createGhostUpdateAssignments(
					ghostUpdateMap.get(new GhostUpdateLocation(statement.getLocation(), false)));

			switch (statement) {
			case final IfStatement ifStmt:
				newStatements.add(annotationCheck);
				newStatements.addAll(processIfStatement(ifStmt));
				break;
			case final WhileStatement whileStmt:
				newStatements.addAll(processWhileStatement(whileStmt, annotationCheck));
				break;

			case final GotoStatement gotoStmt:
				throw new UnsupportedOperationException("Goto statements not yet supported");
			case final BreakStatement breakStmt:
				throw new UnsupportedOperationException("Break statements not yet supported");
			case final ReturnStatement retStmt:
				throw new UnsupportedOperationException("Return statements not yet supported");
			case final CallStatement callStmt:
				throw new UnsupportedOperationException("Procedure calls in concurrent programs must be inlined");

			case final JoinStatement joinStmt:
				// add tid when joined
				mTidNeedsLinearity.add(new Tid(joinStmt.getThreadID()));
				//$FALL-THROUGH$

			default:
				// case Label _ :
				//
				// case AssertStatement _:
				// case AssignmentStatement _:
				// case AssumeStatement _:
				// case HavocStatement _:
				// case AtomicStatement _:
				//
				// case ForkStatement _:
				newStatements.add(annotationCheck);
				newStatements.add(processStatement(statement));
				newStatements.addAll(positiveGhostUpdates);
				break;
			}

			mTidNeedsLinearity.clear();
			// tempory to make it work TODO
			if (mTranslator.getProgramAndProof().getTemplateVisitor().getAssociationTidMap()
					.get(mProcedureName) != null) {
				mTidNeedsLinearity.addAll(mTranslator.getProgramAndProof().getTemplateVisitor().getAssociationTidMap()
						.get(mProcedureName));
			}
		}

		mAtomicStatementCounter += 1;
		// TODO add parameter

		return newStatements.toArray(Statement[]::new);
	}

	private List<Statement> processIfStatement(final IfStatement ifStmt) {
		final List<Statement> result = new ArrayList<>();

		final var ghostUpdateMap = mTranslator.getProgramAndProof().getGhostUpdateMap();
		final var ghostUpdatePositive = ghostUpdateMap.get(new GhostUpdateLocation(ifStmt.getLoc(), false));
		final var ghostUpdateNegative = ghostUpdateMap.get(new GhostUpdateLocation(ifStmt.getLoc(), true));

		final Expression condition;
		final var variableCollector = new BoogieVariableCollector(ifStmt.getCondition());
		if (variableCollector.usesGlobalVariables()) {
			final var conditionProc =
					mTranslator.addCondition(mProcedureName, mAtomicStatementCounter, ifStmt.getCondition());
			result.add(mTranslator.callCondition(conditionProc, ifStmt.getCondition()));
			condition = getOrCreateConditionVariable();
		} else {
			condition = ifStmt.getCondition();
		}

		final var thenPart =
				concatStatements(createGhostUpdateAssignments(ghostUpdatePositive).toArray(Statement[]::new),
						processStatements(ifStmt.getThenPart()));
		final var elsePart =
				concatStatements(createGhostUpdateAssignments(ghostUpdateNegative).toArray(Statement[]::new),
						processStatements(ifStmt.getElsePart()));

		final var newIfStmt = new IfStatement(ifStmt.getLoc(), condition, thenPart, elsePart);
		result.add(newIfStmt);

		return result;
	}

	private List<Statement> processWhileStatement(final WhileStatement whileStmt, final CallStatement loopInvariant) {
		final List<Statement> result = new ArrayList<>();

		final var ghostUpdateMap = mTranslator.getProgramAndProof().getGhostUpdateMap();
		final var ghostUpdatePositive = ghostUpdateMap.get(new GhostUpdateLocation(whileStmt.getLoc(), false));
		final var ghostUpdateNegative = ghostUpdateMap.get(new GhostUpdateLocation(whileStmt.getLoc(), true));

		final Expression condition;
		final Statement[] prologue;
		final var variableCollector = new BoogieVariableCollector(whileStmt.getCondition());
		if (variableCollector.usesGlobalVariables() || ghostUpdatePositive != null) {
			// In these cases, we need to transform the loop into a while(true) loop and evaluate the condition at the
			// start of the body. If it does not hold, we break from the loop.

			final Statement assignCondition;
			if (variableCollector.usesGlobalVariables()) {
				final var conditionProc =
						mTranslator.addCondition(mProcedureName, mAtomicStatementCounter, whileStmt.getCondition());
				assignCondition = mTranslator.callCondition(conditionProc, whileStmt.getCondition());
			} else {
				assignCondition = new AssignmentStatement(null, new LeftHandSide[] { getOrCreateConditionLHS() },
						new Expression[] { whileStmt.getCondition() });
			}

			final var ifNotConditionBreak = new IfStatement(null,
					new UnaryExpression(null, UnaryExpression.Operator.LOGICNEG, getOrCreateConditionVariable()),
					new Statement[] { new BreakStatement(null) }, new Statement[0]);

			prologue = concatStatements(new Statement[] { assignCondition, ifNotConditionBreak },
					createGhostUpdateAssignments(ghostUpdatePositive).toArray(Statement[]::new));
			condition = new BooleanLiteral(null, true);
		} else {
			// In this case, we do not transform the loop and use the original loop condition.
			prologue = new Statement[0];
			condition = whileStmt.getCondition();
		}

		final Statement[] body = processStatements(whileStmt.getBody());

		final var loopYieldsTrue = new LoopInvariantSpecification(null, false, new BooleanLiteral(null, true));
		new CivlAttributesAnnotation(CivlUtils.createYieldsAttribute()).annotate(loopYieldsTrue);

		final LoopInvariantSpecification[] loopInvariantSpecs = { loopYieldsTrue,
				new LoopInvariantSpecification(null, false, CivlUtils.createYieldCallExpression(loopInvariant)) };

		final var newWhileStmt =
				new WhileStatement(null, condition, loopInvariantSpecs, concatStatements(prologue, body));
		result.add(newWhileStmt);

		// add ghost updates for loop exit
		result.addAll(createGhostUpdateAssignments(ghostUpdateNegative));

		return result;
	}

	/**
	 * Rewrites a single statement into its Civl equivalent.
	 *
	 * <p>
	 * Statements that interact with shared state are replaced by calls to generated atomic actions, while
	 * thread-management statements are translated into Civl fork and join procedures.
	 * </p>
	 *
	 * @param statement
	 *            the statement to transform
	 * @return the transformed statement
	 */
	@Override
	protected Statement processStatement(final Statement statement) {
		switch (statement) {
		case final Label label:
			return label;

		case final ForkStatement forkStmt:
			return processForkStatement(forkStmt);
		case final JoinStatement joinStmt:
			return processJoinStatement(joinStmt);

		case final AssertStatement assertStmt:
			return processSimpleStatement(assertStmt);
		case final AssignmentStatement assignStmt:
			return processSimpleStatement(assignStmt);
		case final AssumeStatement assumeStmt:
			return processSimpleStatement(assumeStmt);
		case final HavocStatement havocStmt:
			return processSimpleStatement(havocStmt);

		case final GotoStatement gotoStmt:
			throw new UnsupportedOperationException("Goto statements not yet supported");
		case final BreakStatement breakStmt:
			throw new UnsupportedOperationException("Break statements not yet supported");
		case final ReturnStatement retStmt:
			throw new UnsupportedOperationException("Return statements not yet supported");
		case final AtomicStatement stomicStmt:
			throw new UnsupportedOperationException("Atomic statements not yet supported");
		case final CallStatement callStmt:
			throw new UnsupportedOperationException("Procedure calls in concurrent programs must be inlined");

		case final IfStatement ifStmt:
			throw new IllegalStateException("`if` statements should be handled by processStatements()");
		case final WhileStatement whileStmt:
			throw new IllegalStateException("`while` statements should be handled by processStatements()");
		}
	}

	private Statement processForkStatement(final ForkStatement forkStmt) {
		// TODO support fork parameters
		assert forkStmt.getArguments().length == 0 : "Arguments for forks are not yet supported";

		final Expression[] forkThreadId = forkStmt.getThreadID();
		final String procName = forkStmt.getProcedureName();

		final Expression[] tids = { new IdentifierExpression(forkStmt.getLoc(), BoogieType.createPlaceholderType(0),
				(new Tid(forkThreadId)).toString(), DeclarationInformation.DECLARATIONINFO_GLOBAL) };

		final var newFork = new CallStatement(forkStmt.getLoc(), new NamedAttribute[0], false, new VariableLHS[0],
				"fork_" + procName, tids);
		ModelUtils.copyAnnotations(forkStmt, newFork);
		return newFork;
	}

	private Statement processJoinStatement(final JoinStatement joinStmt) {
		// TODO support return values from joins
		assert joinStmt.getLhs().length == 0 : "Return values from joins are not yet supported";

		final Expression[] joinThreadId = joinStmt.getThreadID();
		final Expression[] tid = { new IdentifierExpression(joinStmt.getLoc(), BoogieType.createPlaceholderType(0),
				new Tid(joinThreadId).toString(), DeclarationInformation.DECLARATIONINFO_GLOBAL) };

		final var newJoin =
				new CallStatement(joinStmt.getLoc(), new NamedAttribute[0], false, new VariableLHS[0], "join", tid);
		ModelUtils.copyAnnotations(joinStmt, newJoin);
		return newJoin;
	}

	private Statement processSimpleStatement(final Statement statement) {
		assert statement instanceof AssertStatement || statement instanceof AssignmentStatement
				|| statement instanceof AssumeStatement || statement instanceof HavocStatement
				: "statement is not a simple statement: " + statement;

		final Statement newStatement;
		final var variableCollector = new BoogieVariableCollector(statement);
		if (variableCollector.usesGlobalVariables()) {
			final var statementProc =
					mTranslator.addAtomicStatement(mProcedureName, mAtomicStatementCounter, statement);
			newStatement = mTranslator.callAtomicStatement(statementProc, statement);
		} else {
			final NamedAttribute[] layer =
					{ CivlUtils.createLayerAttribute(Translator.LAYER_IMPLEMENTATIONS, Translator.LAYER_TOP) };

			if (statement instanceof final AssertStatement assertStmt) {
				newStatement = new AssertStatement(assertStmt.getLoc(), layer, assertStmt.getFormula());
			} else if (statement instanceof final AssumeStatement assumeStmt) {
				newStatement = new AssumeStatement(assumeStmt.getLoc(), layer, assumeStmt.getFormula());
			} else {
				return statement;
			}
		}

		ModelUtils.copyAnnotations(statement, newStatement);
		return newStatement;
	}

	private static List<CallStatement> createGhostUpdateAssignments(final Map<String, Expression> updates) {
		if (updates == null) {
			return List.of();
		}
		final List<CallStatement> assignments = new ArrayList<>();
		for (final var update : updates.entrySet()) {
			assignments.add(createGhostUpdateAssignment(update.getKey(), update.getValue()));
		}
		return assignments;
	}

	private static CallStatement createGhostUpdateAssignment(final String variableName, final Expression value) {
		return new CallStatement(null,
				new NamedAttribute[] { CivlUtils.createLayerAttribute(Translator.LAYER_GHOST_VARS) }, false,
				new VariableLHS[] { new VariableLHS(null, variableName) }, "Copy", new Expression[] { value });
	}

	private IdentifierExpression getOrCreateConditionVariable() {
		ensureConditionVariableDeclaration();
		final var variableName = mConditionVariable.getVariables()[0].getIdentifiers()[0];
		final var type = mConditionVariable.getVariables()[0].getType();
		return new IdentifierExpression(null, type.getBoogieType(), variableName,
				new DeclarationInformation(StorageClass.LOCAL, mProcedureName));
	}

	private VariableLHS getOrCreateConditionLHS() {
		ensureConditionVariableDeclaration();
		final var variableName = mConditionVariable.getVariables()[0].getIdentifiers()[0];
		final var type = mConditionVariable.getVariables()[0].getType();
		return new VariableLHS(null, type.getBoogieType(), variableName,
				new DeclarationInformation(StorageClass.LOCAL, mProcedureName));
	}

	private void ensureConditionVariableDeclaration() {
		if (mConditionVariable == null) {
			mConditionVariable = new VariableDeclaration(null, new Attribute[0],
					new VarList[] { new VarList(null, new String[] { "condition" }, new PrimitiveType(null, "bool")) });
		}
	}

	private static Statement[] concatStatements(final Statement[] first, final Statement[] second) {
		if (first.length == 0) {
			return second;
		}
		if (second.length == 0) {
			return first;
		}

		final Statement[] result = new Statement[first.length + second.length];
		System.arraycopy(first, 0, result, 0, first.length);
		System.arraycopy(second, 0, result, first.length, second.length);
		return result;
	}
}
