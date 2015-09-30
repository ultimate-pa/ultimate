package de.uni_freiburg.informatik.ultimate.source.java;

import java.util.List;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.ExpressionStatement;
import org.joogie.boogie.statements.InvokeStatement;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class StatementTranslator extends JoogieStatementTransformer<Statement> {

	private final Logger mLogger;
	private final ILocation mLocation;
	private final Statement mStatement;

	private StatementTranslator(Logger logger, ILocation location, org.joogie.boogie.statements.Statement stmt) {
		mLogger = logger;
		mLocation = location;
		mStatement = visit(stmt);
	}

	private Statement getTranslation() {
		return mStatement;
	}

	public static Statement translate(Logger logger, ILocation location, org.joogie.boogie.statements.Statement stmt) {
		return new StatementTranslator(logger, location, stmt).getTranslation();
	}

	@Override
	protected Statement visit(org.joogie.boogie.statements.AssertStatement stmt) {
		return new AssertStatement(mLocation, ExpressionTranslator.translate(mLogger, mLocation, stmt.getExpression()));
	}

	@Override
	protected Statement visit(AssignStatement stmt) {
		final IdentifierExpression left = (IdentifierExpression) ExpressionTranslator.translate(mLogger, mLocation,
				stmt.getLeft());
		final Expression right = ExpressionTranslator.translate(mLogger, mLocation, stmt.getRight());
		return new AssignmentStatement(mLocation,
				new VariableLHS[] { new VariableLHS(mLocation, left.getIdentifier()) }, new Expression[] { right });
	}

	@Override
	protected Statement visit(org.joogie.boogie.statements.AssumeStatement stmt) {
		return new AssumeStatement(mLocation, ExpressionTranslator.translate(mLogger, mLocation, stmt.getExpression()));
	}

	@Override
	protected Statement visit(ExpressionStatement stmt) {
		// this is used for a function call (????) -- kill it were it stands!
		throw new UnsupportedOperationException();
	}

	@Override
	protected Statement visit(InvokeStatement stmt) {
		final List<VariableLHS> lhs = stmt.getReturnTargets().stream()
				.map(a -> new VariableLHS(mLocation,
						((IdentifierExpression) ExpressionTranslator.translate(mLogger, mLocation, a)).getIdentifier()))
				.collect(Collectors.toList());
		final List<Expression> arguments = stmt.getArguments().stream()
				.map(a -> ExpressionTranslator.translate(mLogger, mLocation, a)).collect(Collectors.toList());
		return new CallStatement(mLocation, false, lhs.toArray(new VariableLHS[lhs.size()]),
				stmt.getInvokedProcedure().getName(), arguments.toArray(new Expression[arguments.size()]));
	}

	@Override
	protected Statement visit(org.joogie.boogie.statements.HavocStatement stmt) {
		final List<VariableLHS> identifiers = stmt.getHavocVars().stream()
				.map(a -> new VariableLHS(mLocation, a.getName())).collect(Collectors.toList());
		return new HavocStatement(mLocation, identifiers.toArray(new VariableLHS[identifiers.size()]));
	}

	@Override
	protected Statement visit(org.joogie.boogie.statements.ReturnStatement stmt) {
		return new ReturnStatement(mLocation);
	}
}
