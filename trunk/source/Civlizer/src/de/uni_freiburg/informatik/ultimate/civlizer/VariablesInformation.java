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

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;

/**
 * Collects information about variable usage in procedures and annotations.
 *
 * <p>
 * For every statement inside a procedure, this visitor records the identifiers that refer to local and global
 * variables. It also records which local variables occur in the annotation expressions of the program.
 *
 * <p>
 * Local variables are determined from the lexical scope of the currently visited procedure body. All identifiers that
 * are not local variables are considered global variables.
 *
 * <p>
 * The collected information is used by Civlizer to determine whether a statement or annotation depends on local or
 * global state.
 */
final class VariablesInformation extends BoogieVisitor {

	private boolean mInProcedure;
	private final Deque<String> mCurrentLocalVariables = new ArrayDeque<>();
	private final Set<String> mLocalVariableIds = new HashSet<>();
	private final Set<String> mGlobalVariableIds = new HashSet<>();
	private Statement mCurrentStatement;
	private Expression mCurrentExpression;
	private final Map<Statement, Set<IdentifierExpression>> mLocalStatementMap = new HashMap<>();
	private final Map<Statement, Set<IdentifierExpression>> mGlobalStatementMap = new HashMap<>();
	private final Map<Expression, Set<IdentifierExpression>> mExpressionMap = new HashMap<>();

	VariablesInformation(final ProgramAndProof programAndProof) {
		// For the program
		mInProcedure = true;
		for (final Declaration declaration : programAndProof.getBoogieAst().getDeclarations()) {
			processDeclaration(declaration);

			if (declaration instanceof final Procedure procedure) {
				visit(procedure);
			} else if (declaration instanceof final VariableDeclaration variableDeclaration) {
				collectGlobalVariables(variableDeclaration);
			}
		}

		// For the proof
		mInProcedure = false;
		for (final Expression expression : programAndProof.getAnnotationMap().values()) {
			mCurrentExpression = expression;
			processExpression(expression);
		}
	}

	Map<Statement, Set<IdentifierExpression>> getLocalStatementMap() {
		return mLocalStatementMap;
	}

	Map<Statement, Set<IdentifierExpression>> getGlobalStatementMap() {
		return mGlobalStatementMap;
	}

	Map<Expression, Set<IdentifierExpression>> getExpressionMap() {
		return mExpressionMap;
	}

	/**
	 * Returns whether the given statement accesses at least one local variable.
	 */
	boolean containLocalVars(final Statement statement) {
		return containsVariable(statement, mLocalStatementMap, mLocalVariableIds);
	}

	/**
	 * Returns whether the given statement accesses at least one global variable.
	 */
	boolean containGlobalVars(final Statement statement) {
		return containsVariable(statement, mGlobalStatementMap, mGlobalVariableIds);
	}

	@Override
	protected Body processBody(final Body body) {
		final int numberOfLocals = collectLocalVariables(body);

		final Body processedBody = super.processBody(body);

		/*
		 * Restore the local-variable scope after leaving the body. This is important because the same visitor instance
		 * traverses multiple procedure bodies.
		 */
		for (int i = 0; i < numberOfLocals; i++) {
			final String variable = mCurrentLocalVariables.pop();
			mLocalVariableIds.remove(variable);
		}

		return processedBody;
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		mCurrentStatement = statement;
		return super.processStatement(statement);
	}

	@Override
	protected void visit(final IdentifierExpression expression) {
		if (mInProcedure) {
			recordVariableAccess(mCurrentStatement, expression,
					isLocalVariable(expression.getIdentifier()) ? mLocalStatementMap : mGlobalStatementMap);
		} else if (containsLocalVariable(expression)) {
			recordVariableAccess(mCurrentExpression, expression, mExpressionMap);
		}
	}

	@Override
	protected void visit(final VariableLHS lhs) {
		final IdentifierExpression expression = new IdentifierExpression(lhs.getLoc(), lhs.getType(),
				lhs.getIdentifier(), lhs.getDeclarationInformation());

		recordVariableAccess(mCurrentStatement, expression,
				isLocalVariable(expression.getIdentifier()) ? mLocalStatementMap : mGlobalStatementMap);
	}

	/**
	 * Collects all global variable identifiers declared by a Boogie variable declaration.
	 */
	private void collectGlobalVariables(final VariableDeclaration declaration) {
		for (final VarList variableList : declaration.getVariables()) {
			Collections.addAll(mGlobalVariableIds, variableList.getIdentifiers());
		}
	}

	/**
	 * Adds the local variables declared by {@code body} to the current scope.
	 *
	 * @return the number of variables added, used to restore the scope after traversal
	 */
	private int collectLocalVariables(final Body body) {
		int numberOfLocals = 0;

		for (final VariableDeclaration declaration : body.getLocalVars()) {
			for (final VarList variableList : declaration.getVariables()) {
				for (final String identifier : variableList.getIdentifiers()) {
					mCurrentLocalVariables.push(identifier);
					mLocalVariableIds.add(identifier);
					numberOfLocals++;
				}
			}
		}

		return numberOfLocals;
	}

	/**
	 * Records an identifier expression in the map associated with the current AST node.
	 */
	private static <T> void recordVariableAccess(final T node, final IdentifierExpression expression,
			final Map<T, Set<IdentifierExpression>> map) {

		map.computeIfAbsent(node, ignored -> new HashSet<>()).add(expression);
	}

	/**
	 * Checks whether the given identifier belongs to the currently active local-variable scope.
	 */
	private boolean isLocalVariable(final String identifier) {
		return mLocalVariableIds.contains(identifier);
	}

	/**
	 * Checks whether an annotation expression references a local variable.
	 *
	 * <p>
	 * This is intentionally based on the set of local variable identifiers collected during the procedure traversal.
	 */
	private boolean containsLocalVariable(final IdentifierExpression expression) {
		return isLocalVariable(expression.getIdentifier());
	}

	private static boolean containsVariable(final Statement statement,
			final Map<Statement, Set<IdentifierExpression>> variableMap, final Set<String> variableIds) {

		return variableMap.getOrDefault(statement, Collections.emptySet()).stream()
				.map(IdentifierExpression::getIdentifier).anyMatch(variableIds::contains);
	}
}
