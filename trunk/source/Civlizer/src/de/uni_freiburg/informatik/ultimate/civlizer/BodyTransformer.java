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
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
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
 */
final class BodyTransformer extends BoogieTransformer {

	private final ILogger mLogger;
	private final Translator mTranslator;
	private String mCurrentProcedure;
	private IdentifierExpression[] mCurrentTids;
	private Set<Tid> mTidNeedsLinearity;
	private int mAtomicStatementCounter;

	/**
	 * Creates a new body transformer.
	 *
	 * @param programAndProof
	 *            the program together with its proof annotations and thread information
	 */
	BodyTransformer(final IUltimateServiceProvider services, final Translator translator) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mTranslator = translator;
		mCurrentProcedure = null;
		mCurrentTids = null;
		mTidNeedsLinearity = null;
		mAtomicStatementCounter = 0;
	}

	private void setCurrentProcedure(final String name, final IdentifierExpression[] tids) {
		if (mCurrentProcedure != name) {
			mCurrentProcedure = name;
			mCurrentTids = tids;
			// TODO maybe use mAllTidMap
			mTidNeedsLinearity = new HashSet<>(mTranslator.getProgramAndProof().getTemplateVisitor().getTids());
			mAtomicStatementCounter = 0;
		}
	}

	private static List<Expression> tidListToArrayExpression(final List<Tid> tidList) {
		return tidList.stream().map(tid -> (Expression) new IdentifierExpression(null, /*
																						 * maybe to be change TODO or
																						 * not
																						 */
				BoogieType.createPlaceholderType(0), tid.toString(),
				new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null))).toList();
	}

	/**
	 * Transforms the body of a procedure into its CIVL representation.
	 *
	 * @param name
	 *            the procedure name
	 * @param body
	 *            the original Boogie procedure body
	 * @return the transformed body
	 */
	Body transformBody(final String name, final Body body) {

		final int size = mTranslator.getProgramAndProof().getTemplateVisitor().getAllTidMap()
				.getOrDefault(name, Collections.emptyList()).size()
				+ (name.equals(BoogieUtils.START_PROCEDURE) ? 1 : 0);

		final IdentifierExpression[] tids = new IdentifierExpression[size];

		int i = 0;

		if (name.equals(BoogieUtils.START_PROCEDURE)) {
			tids[i] = new IdentifierExpression(null, BoogieType.createPlaceholderType(0), "start_tid",
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null));
			i++;
		}

		for (final Tid tid : mTranslator.getProgramAndProof().getTemplateVisitor().getAllTidMap().getOrDefault(name,
				Collections.emptyList())) {
			tids[i] = new IdentifierExpression(null, BoogieType.createPlaceholderType(0), tid.toString(),
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null));
			i++;
		}

		setCurrentProcedure(name, tids);

		return processBody(body);
	}

	@Override
	protected Body processBody(final Body body) {
		final var newBody = super.processBody(body);

		final var newStatements = new ArrayList<>(Arrays.asList(newBody.getBlock()));

		final Expression annotation =
				mTranslator.getProgramAndProof().getTemplateVisitor().getExitAnnotationMap().get(mCurrentProcedure);
		mTranslator.addYieldInvariants(mCurrentProcedure, mAtomicStatementCounter, annotation, null,
				mTidNeedsLinearity);
		newStatements.add(
				mTranslator.callYieldInvariants(mCurrentProcedure, mAtomicStatementCounter, mCurrentTids, annotation));

		if (mCurrentProcedure != BoogieUtils.START_PROCEDURE) {
			newStatements.add(new CallStatement(null, new NamedAttribute[0], false, new VariableLHS[0], "terminate",
					mCurrentTids));
		}
		return new Body(newBody.getLoc(), newBody.getLocalVars(), newStatements.toArray(Statement[]::new));
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

		// param
		final var inParams = new ArrayList<ParameterDeclaration>();

		if (BoogieUtils.START_PROCEDURE.equals(mCurrentProcedure)) {
			inParams.add(new ParameterDeclaration("start_tid", Translator.makeOne(mTranslator.getStartTidType()),
					Linearity.INOUT));
		}

		for (final Tid tid : mTranslator.getProgramAndProof().getTemplateVisitor().getAllTidMap()
				.getOrDefault(mCurrentProcedure, Collections.emptyList())) {
			inParams.add(new ParameterDeclaration(tid.toString(), Translator.makeOne(mTranslator.getTidType()),
					Linearity.IN));
		}

		// annotation map
		final Map<ILocation, Expression> annotationMap = mTranslator.getProgramAndProof().getAnnotationMap();
		mLogger.warn(annotationMap);

		for (final Statement statement : statements) { // ignore standard return
			// skip return for now
			if (statement instanceof ReturnStatement) {
				continue;
			}

			mAtomicStatementCounter += 1;

			final boolean globalVar = mTranslator.getVariablesInformation().containGlobalVars(statement);
			final boolean localVar = mTranslator.getVariablesInformation().containLocalVars(statement);

			final var annotation = annotationMap.get(statement.getLoc());
			mTranslator.addYieldInvariants(mCurrentProcedure, mAtomicStatementCounter, annotation, null,
					mTidNeedsLinearity);
			newStatements.add(mTranslator.callYieldInvariants(mCurrentProcedure, mAtomicStatementCounter, mCurrentTids,
					annotation));

			if (statement instanceof final IfStatement ifStmt) {

				mTranslator.addCondition(mCurrentProcedure, mAtomicStatementCounter, ifStmt.getCondition());
				newStatements.add(
						mTranslator.callCondition(mCurrentProcedure, mAtomicStatementCounter, ifStmt.getCondition()));
				newStatements
						.add(new IfStatement(ifStmt.getLoc(), new IdentifierExpression(ifStmt.getLoc(), "condition"),
								processStatements(ifStmt.getThenPart()), processStatements(ifStmt.getElsePart())));

			} else if (statement instanceof final WhileStatement whileStmt) {

				mTranslator.addCondition(mCurrentProcedure, mAtomicStatementCounter, whileStmt.getCondition());
				final Statement assignCondition =
						mTranslator.callCondition(mCurrentProcedure, mAtomicStatementCounter, whileStmt.getCondition());

				final Statement[] body = processStatements(whileStmt.getBody());
				final CallStatement firstAnnotation = (CallStatement) body[0];
				final LoopInvariantSpecification[] loopInvariant =
						{ new LoopInvariantSpecification(null, false, new BooleanLiteral(null, true)),
								new LoopInvariantSpecification(null, false, new FunctionApplication(null,
										firstAnnotation.getMethodName(), firstAnnotation.getArguments())) };

				// test invariant TODO change
				newStatements.add(assignCondition);
				newStatements.add(new WhileStatement(null, new IdentifierExpression(whileStmt.getLoc(), "condition"),
						loopInvariant, Stream.concat(Arrays.stream(body), Stream.of(firstAnnotation, assignCondition))
								.toArray(Statement[]::new)));

			} else if (statement instanceof ForkStatement || globalVar && !localVar) {
				newStatements.add(processStatement(statement));
			} else if (statement instanceof final JoinStatement joinStmt) {
				// add tid when joined
				mTidNeedsLinearity.add(new Tid(joinStmt.getThreadID()));
				newStatements.add(processStatement(statement));
			} else if (!globalVar) {

				final NamedAttribute[] layer = { new NamedAttribute(statement.getLoc(), "layer", new Expression[] {
						new IntegerLiteral(statement.getLoc(), "1"), new IntegerLiteral(statement.getLoc(), "2") }) };

				if (statement instanceof final AssertStatement assertStmt) {
					newStatements.add(new AssertStatement(assertStmt.getLoc(), layer, assertStmt.getFormula()));
				} else if (statement instanceof final AssumeStatement assumeStmt) {
					newStatements.add(new AssumeStatement(assumeStmt.getLoc(), layer, assumeStmt.getFormula()));
				} else if (statement instanceof final Label labelStmt) {
					newStatements.add(new Label(labelStmt.getLoc(), labelStmt.getName()));
				}
				/*
				 * else if (statements[i] instanceof final HavocStatement havoc) { maybe havoc }
				 */
				else {
					newStatements.add(statement);
				}
			} else {
				mTranslator.addStatement(mCurrentProcedure, statement, mTidNeedsLinearity, mAtomicStatementCounter);
				newStatements
						.add(mTranslator.callAtomicStatement(mCurrentProcedure, statement, mAtomicStatementCounter));
			}

			// Ghost update
			if (mTranslator.getProgramAndProof().getGhostUpdateMap() != null
					&& mTranslator.getProgramAndProof().getGhostUpdateMap().get(statement.getLocation()) != null) {
				newStatements.addAll(mTranslator.getProgramAndProof().getGhostUpdateMap().get(statement.getLocation()));
			}

			mTidNeedsLinearity.clear();
			// tempory to make it work TODO
			if (mTranslator.getProgramAndProof().getTemplateVisitor().getAssociationTidMap()
					.get(mCurrentProcedure) != null) {
				mTidNeedsLinearity.addAll(mTranslator.getProgramAndProof().getTemplateVisitor().getAssociationTidMap()
						.get(mCurrentProcedure));
			}
		}

		mAtomicStatementCounter += 1;
		// TODO add parameter

		return newStatements.toArray(Statement[]::new);
	}

	/**
	 * Process array of local variable declarations. This is called for implementations.
	 *
	 * @param locals
	 *            the array of variable declarations
	 * @return the processed declarations.
	 */
	// TODO put it in the condition
	@Override
	protected VariableDeclaration[] processLocalVariableDeclarations(final VariableDeclaration[] locals) {
		final VariableDeclaration[] newLocals = new VariableDeclaration[locals.length + 1];
		for (int i = 0; i < locals.length; i++) {
			newLocals[i] = processLocalVariableDeclaration(locals[i]);
		}
		newLocals[locals.length] = new VariableDeclaration(null, new Attribute[0],
				new VarList[] { new VarList(null, new String[] { "condition" }, new PrimitiveType(null, "bool")) });
		return newLocals;
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
		Statement newStatement = null;
		// Label, IfStatement, AssignmentStatement, ReturnStatement, ForkStatement, CallStatement, JoinStatement,
		// AssertStatement, WhileStatement, GotoStatement, AtomicStatement, AssumeStatement, BreakStatement,
		// HavocStatement
		if (statement instanceof AssertStatement || statement instanceof AssignmentStatement
				|| statement instanceof AssumeStatement || statement instanceof AtomicStatement
				|| statement instanceof HavocStatement) {
			mTranslator.addStatement(mCurrentProcedure, statement, mTidNeedsLinearity, mAtomicStatementCounter);
			newStatement = mTranslator.callAtomicStatement(mCurrentProcedure, statement, mAtomicStatementCounter);
		} else if (statement instanceof final CallStatement call) {
			throw new UnsupportedOperationException("Procedure Call");

		} else if (statement instanceof final ForkStatement forkstmt) {
			final Expression[] threadId = forkstmt.getThreadID();
			final String procName = forkstmt.getProcedureName();

			final Expression[] tids = { new IdentifierExpression(forkstmt.getLoc(), BoogieType.createPlaceholderType(0),
					(new Tid(threadId)).toString(),
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)) };

			newStatement = new CallStatement(forkstmt.getLoc(), new NamedAttribute[0], false, new VariableLHS[0],
					"fork_" + procName, tids); // add expression TODO

		} else if (statement instanceof final JoinStatement joinstmt) {
			final Expression[] threadId = joinstmt.getThreadID();

			final Expression[] tid = { new IdentifierExpression(joinstmt.getLoc(), BoogieType.createPlaceholderType(0),
					(new Tid(threadId)).toString(),
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)) };

			// VariableLHS[] out = new VariableLHS[] {
			// new VariableLHS(joinstmt.getLoc(), "out" + ((new Tid(threadId)).toString()).substring(3))
			// }; Maybe laiter

			newStatement =
					new CallStatement(joinstmt.getLoc(), new NamedAttribute[0], false, new VariableLHS[0], "join", tid); // LHS
																															// TODO
		}

		if (newStatement == null) {
			/* No recursion for label, havoc, break, return and goto */
			return statement;
		}
		ModelUtils.copyAnnotations(statement, newStatement);
		return newStatement;
	}
}
