package de.uni_freiburg.informatik.ultimate.source.java.joogie;

import org.joogie.boogie.statements.AssertStatement;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.boogie.statements.ExpressionStatement;
import org.joogie.boogie.statements.HavocStatement;
import org.joogie.boogie.statements.InvokeStatement;
import org.joogie.boogie.statements.ReturnStatement;
import org.joogie.boogie.statements.Statement;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class JoogieStatementTransformer<T> {

	protected T visit(Statement stmt) {
		if (stmt instanceof AssertStatement) {
			return visit((AssertStatement) stmt);
		} else if (stmt instanceof AssignStatement) {
			return visit((AssignStatement) stmt);
		} else if (stmt instanceof AssumeStatement) {
			return visit((AssumeStatement) stmt);
		} else if (stmt instanceof ExpressionStatement) {
			return visit((ExpressionStatement) stmt);
		} else if (stmt instanceof HavocStatement) {
			return visit((HavocStatement) stmt);
		} else if (stmt instanceof InvokeStatement) {
			return visit((InvokeStatement) stmt);
		} else if (stmt instanceof ReturnStatement) {
			return visit((ReturnStatement) stmt);
		} else {
			throw new UnsupportedOperationException(
					"Statement type not implemented: " + stmt == null ? "null" : stmt.getClass().getSimpleName());
		}
	}

	protected T visit(AssertStatement stmt) {
		return null;
	}

	protected T visit(AssignStatement stmt) {
		return null;
	}

	protected T visit(AssumeStatement stmt) {
		return null;
	}

	protected T visit(ExpressionStatement stmt) {
		return null;
	}

	protected T visit(HavocStatement stmt) {
		return null;
	}

	protected T visit(InvokeStatement stmt) {
		return null;
	}

	protected T visit(ReturnStatement stmt) {
		return null;
	}
}
