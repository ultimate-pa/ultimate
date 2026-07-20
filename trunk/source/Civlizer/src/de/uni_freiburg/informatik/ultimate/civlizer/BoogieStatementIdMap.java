package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;

// TODO local var change name
final class BoogieStatementIdMap extends BoogieVisitor {

	private final Deque<IdentifierExpression> mCurrentLocalVariables = new ArrayDeque<>();
	private Statement mCurrentStatement = null;
	private Expression mCurrentExpression = null;
	private final Map<Statement, Set<IdentifierExpression>> mStatementMap = new HashMap<>();
	private final Map<Expression, Set<IdentifierExpression>> mExpressionMap = new HashMap<>();

	BoogieStatementIdMap(final Unit boogieAst) {
		for (final Declaration decl : boogieAst.getDeclarations()) {
			processDeclaration(decl);
		}
	}

	Map<Statement, Set<IdentifierExpression>> getStatementMap() {
		return mStatementMap;
	}

	Map<Expression, Set<IdentifierExpression>> getExpressionMap() {
		return mExpressionMap;
	}

	@Override
	protected Body processBody(final Body body) {
		int nVars = 0;

		for (final VariableDeclaration varDecl : body.getLocalVars()) {
			for (final VarList varList : varDecl.getVariables()) {
				for (final String id : varList.getIdentifiers()) {
					nVars++;
					mCurrentLocalVariables.push(new IdentifierExpression(null, varList.getType().getBoogieType(), id,
							DeclarationInformation.DECLARATIONINFO_GLOBAL));
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

	@Override
	public Expression processExpression(final Expression expr) {
		mCurrentExpression = expr;
		return super.processExpression(expr);
	}

	@Override
	protected void visit(final IdentifierExpression expr) {
		// TODO change idSet name maybe
		if (mCurrentLocalVariables.contains(expr)) {
			Set<IdentifierExpression> idSet = mStatementMap.get(mCurrentStatement);

			if (idSet == null) {
				idSet = new HashSet<>();
				mStatementMap.put(mCurrentStatement, idSet);
			}

			idSet.add(expr);

			idSet = mExpressionMap.get(mCurrentStatement);

			if (idSet == null) {
				idSet = new HashSet<>();
				mStatementMap.put(mCurrentStatement, idSet);
			}

			idSet.add(expr);
		}
	}
}
