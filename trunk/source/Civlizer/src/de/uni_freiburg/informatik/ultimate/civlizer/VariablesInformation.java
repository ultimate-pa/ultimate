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

final class VariablesInformation extends BoogieVisitor {

	private boolean mProcFlag;
	private final Deque<String> mCurrentLocalVariables = new ArrayDeque<>();
	private Statement mCurrentStatement = null;
	private Expression mCurrentExpression = null;
	private final Map<Statement, Set<IdentifierExpression>> mLocalStatementMap = new HashMap<>();
	private final Map<Statement, Set<IdentifierExpression>> mGlobalStatementMap = new HashMap<>();
	private final Map<Expression, Set<IdentifierExpression>> mExpressionMap = new HashMap<>();
	private final Set<String> mLocalVariableIds = new HashSet<>();
	private final Set<String> mGlobalVariableIds = new HashSet<>();

	VariablesInformation(final ProgramAndProof programAndProof) {

		mProcFlag = true;
		for (final Declaration decl : programAndProof.getBoogieAst().getDeclarations()) {
			processDeclaration(decl);
			if (decl instanceof final Procedure proc) {
				visit(proc);
			} else if (decl instanceof final VariableDeclaration varDecl) {
				for (final VarList varList : varDecl.getVariables()) {
					Collections.addAll(mGlobalVariableIds, varList.getIdentifiers());
				}
			}
		}

		mProcFlag = false;
		for (final Expression expr : programAndProof.getAnnotationMap().values()) {
			mCurrentExpression = expr;
			processExpression(expr);
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

	boolean containLocalVars(final Statement statement) {
		return mLocalStatementMap.getOrDefault(statement, Collections.emptySet()).stream()
				.map(IdentifierExpression::getIdentifier).anyMatch(mLocalVariableIds::contains);
	}

	boolean containGlobalVars(final Statement statement) {
		return mGlobalStatementMap.getOrDefault(statement, Collections.emptySet()).stream()
				.map(IdentifierExpression::getIdentifier).anyMatch(mGlobalVariableIds::contains);
	}

	@Override
	protected Body processBody(final Body body) {
		int nVars = 0;

		for (final VariableDeclaration varDecl : body.getLocalVars()) {
			for (final VarList varList : varDecl.getVariables()) {
				for (final String id : varList.getIdentifiers()) {
					nVars++;
					mCurrentLocalVariables.push(id);
					mLocalVariableIds.add(id);
				}
			}
		}

		final Body newBody = super.processBody(body);

		for (; 0 < nVars; nVars--) {
			mCurrentLocalVariables.pop();
		}

		return newBody;
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		mCurrentStatement = statement;
		return super.processStatement(statement);
	}

	/*
	 * @Override public Expression processExpression(final Expression expr) { mCurrentExpression = expr; return
	 * super.processExpression(expr); }
	 */

	@Override
	protected void visit(final IdentifierExpression expr) {
		// TODO change idSet name maybe
		if (mProcFlag) {
			if (mCurrentLocalVariables.stream().anyMatch(id -> id.equals(expr.getIdentifier()))) {
				Set<IdentifierExpression> idSet = mLocalStatementMap.get(mCurrentStatement);

				if (idSet == null) {
					idSet = new HashSet<>();
					mLocalStatementMap.put(mCurrentStatement, idSet);
				}

				idSet.add(expr);
			} else {
				Set<IdentifierExpression> idSet = mGlobalStatementMap.get(mCurrentStatement);

				if (idSet == null) {
					idSet = new HashSet<>();
					mGlobalStatementMap.put(mCurrentStatement, idSet);
				}

				idSet.add(expr);
			}

		} else if (!mProcFlag && mLocalStatementMap.values().stream().anyMatch(
				varSet -> varSet.stream().anyMatch(var -> var.getIdentifier().equals(expr.getIdentifier())))) {
			Set<IdentifierExpression> idSet = mExpressionMap.get(mCurrentExpression);

			if (idSet == null) {
				idSet = new HashSet<>();
				mExpressionMap.put(mCurrentExpression, idSet);
			}

			idSet.add(expr);
		}
	}

	@Override
	protected void visit(final VariableLHS lhs) {
		final IdentifierExpression expr = new IdentifierExpression(lhs.getLoc(), lhs.getType(), lhs.getIdentifier(),
				lhs.getDeclarationInformation());

		if (mCurrentLocalVariables.stream().anyMatch(id -> id.equals(expr.getIdentifier()))) {
			Set<IdentifierExpression> idSet = mLocalStatementMap.get(mCurrentStatement);

			if (idSet == null) {
				idSet = new HashSet<>();
				mLocalStatementMap.put(mCurrentStatement, idSet);
			}

			idSet.add(expr);
		} else {
			Set<IdentifierExpression> idSet = mGlobalStatementMap.get(mCurrentStatement);

			if (idSet == null) {
				idSet = new HashSet<>();
				mGlobalStatementMap.put(mCurrentStatement, idSet);
			}

			idSet.add(expr);
		}
	}
}
