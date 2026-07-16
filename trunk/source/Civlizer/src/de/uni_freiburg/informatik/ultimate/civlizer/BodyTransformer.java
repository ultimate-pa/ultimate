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
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration.Linearity;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

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

	private final Translator mTranslator;
	private String mCurrentProcedure;
	private Expression[] mCurrentTids;
	private Set<Tid> mTidNeedsLinearity;
	private int mAtomicStatementCounter;

	/**
	 * Creates a new body transformer.
	 *
	 * @param programAndProof
	 *            the program together with its proof annotations and thread information
	 */
	BodyTransformer(final Translator translator) {
		mTranslator = translator;
		mCurrentProcedure = null;
		mCurrentTids = null;
		mTidNeedsLinearity = null;
		mAtomicStatementCounter = 0;
	}

	private void setCurrentProcedure(final String name, final Expression[] tids) {
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

		final Expression[] tids = new Expression[size];

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
		final Map<ILocation, Expression> annotationMap =
				mTranslator.getProgramAndProof().getAnnotationMap(mCurrentProcedure);

		for (final Statement statement : statements) { // ignore standard return
			// skip return for now
			if (statement instanceof ReturnStatement) {
				continue;
			}

			mAtomicStatementCounter += 1;

			final boolean globalVar =
					mTranslator.getProgramAndProof().getTemplateVisitor().containsGlobalVariables(statement);

			final boolean localVar = mTranslator.getProgramAndProof().getTemplateVisitor()
					.containsLocalVariables(mCurrentProcedure, statement);

			// invariant test

			mTranslator.addYieldInvariants(mCurrentProcedure, mAtomicStatementCounter,
					annotationMap.get(statement.getLoc()), null, mTidNeedsLinearity);
			newStatements.add(Translator.callYieldInvariants(mCurrentProcedure, mAtomicStatementCounter, mCurrentTids));

			// add statement
			mTranslator.addStatement(mCurrentProcedure, statement, mTidNeedsLinearity, mAtomicStatementCounter);

			if (statement instanceof final IfStatement ifStmt) {
				newStatements.add(new CallStatement(ifStmt.getLocation(), new NamedAttribute[0], false,
						new VariableLHS[] { new VariableLHS(ifStmt.getLocation(), "condition") },
						mCurrentProcedure + "_condition_" + mAtomicStatementCounter,
						new Expression[] { ifStmt.getCondition() }));
				newStatements
						.add(new IfStatement(ifStmt.getLoc(), new IdentifierExpression(ifStmt.getLoc(), "condition"),
								processStatements(ifStmt.getThenPart()), processStatements(ifStmt.getElsePart())));

			} else if (statement instanceof final WhileStatement whileStmt) {
				final int currentCounter = mAtomicStatementCounter;

				// TODO add parameter
				final Statement assignCondition =
						Translator.callCondition(mCurrentProcedure, mAtomicStatementCounter, new Expression[0]);

				newStatements.add(assignCondition);
				newStatements.add(new WhileStatement(whileStmt.getLocation(),
						new IdentifierExpression(whileStmt.getLoc(), "condition"), whileStmt.getInvariants(),
						Stream.concat(Arrays.stream(processStatements(whileStmt.getBody())), Stream.of(assignCondition))
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
				final var loc = statement.getLoc();

				final Expression[] arguments = mTranslator.getProgramAndProof().getTemplateVisitor()
						.getStatementParametersMap().get(loc).stream()
						.map(arg -> new IdentifierExpression(loc, BoogieType.createPlaceholderType(0), arg,
								new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)))
						.toArray(Expression[]::new);

				final VariableLHS[] returns =
						mTranslator.getProgramAndProof().getTemplateVisitor().getStatementParametersMap().get(loc)
								.stream().map(ret -> new VariableLHS(loc, ret)).toArray(VariableLHS[]::new);

				newStatements.add(new CallStatement(statement.getLocation(), new NamedAttribute[0], false, returns,
						mCurrentProcedure + "_stmt_" + mAtomicStatementCounter, arguments));
			}

			// newStatements.add(new CallStatement(statements[i].getLocation(), new NamedAttribute[0], false,
			// new VariableLHS[0], "yield_" + mCurrentProcedure + "_" + mAtomicStatementCounter, tids));

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

		mTranslator.addYieldInvariants(mCurrentProcedure, mAtomicStatementCounter,
				mTranslator.getProgramAndProof().getTemplateVisitor().getExitAnnotationMap().get(mCurrentProcedure),
				null, mTidNeedsLinearity);
		newStatements.add(Translator.callYieldInvariants(mCurrentProcedure, mAtomicStatementCounter, mCurrentTids));

		if (mCurrentProcedure != BoogieUtils.START_PROCEDURE) {
			newStatements.add(new CallStatement(null, new NamedAttribute[0], false, new VariableLHS[0], "terminate",
					mCurrentTids));
		}

		return newStatements.toArray(Statement[]::new);
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
			newStatement = new CallStatement(statement.getLocation(), new NamedAttribute[0], false, new VariableLHS[0],
					mCurrentProcedure + "_stmt_" + mAtomicStatementCounter, new Expression[0]);
		} else if (statement instanceof final CallStatement call) {
			final Expression[] args = call.getArguments();
			final Expression[] newArgs = processExpressions(args);
			final VariableLHS[] lhs = call.getLhs();
			final VariableLHS[] newLhs = processVariableLHSs(lhs);
			final Attribute[] newAttr = processAttributes(call.getAttributes());
			if (args != newArgs || lhs != newLhs || newAttr != call.getAttributes()) {
				newStatement = new CallStatement(call.getLocation(), (NamedAttribute[]) newAttr, call.isForall(),
						newLhs, call.getMethodName(), newArgs);

				// create error
			}
		} else if (statement instanceof final ForkStatement forkstmt) {
			final Expression[] threadId = forkstmt.getThreadID();
			final String procName = forkstmt.getProcedureName();
			final Expression[] arguments = forkstmt.getArguments();
			final Expression[] newThreadId = processExpressions(threadId);
			final Expression[] newArguments = processExpressions(arguments);

			final Expression[] tids = { new IdentifierExpression(forkstmt.getLoc(), BoogieType.createPlaceholderType(0),
					(new Tid(threadId)).toString(),
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)) };

			newStatement = new CallStatement(forkstmt.getLoc(), new NamedAttribute[0], false, new VariableLHS[0],
					"fork_" + procName, tids); // add expression TODO

		} else if (statement instanceof final JoinStatement joinstmt) {
			final Expression[] threadId = joinstmt.getThreadID();
			final VariableLHS[] lhs = joinstmt.getLhs();
			final Expression[] newThreadId = processExpressions(threadId);
			final VariableLHS[] newLhs = processVariableLHSs(lhs);

			// variable out to define TODO

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
