package de.uni_freiburg.informatik.ultimate.source.java.soottocfg;

import soottocfg.cfg.statement.AssertStatement;
import soottocfg.cfg.statement.AssignStatement;
import soottocfg.cfg.statement.AssumeStatement;
import soottocfg.cfg.statement.CallStatement;
import soottocfg.cfg.statement.Statement;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SootToCfgStatementTransformer<T> {

	protected T visit(Statement stmt) {
		if (stmt instanceof AssertStatement) {
			return visit((AssertStatement) stmt);
		} else if (stmt instanceof AssignStatement) {
			return visit((AssignStatement) stmt);
		} else if (stmt instanceof AssumeStatement) {
			return visit((AssumeStatement) stmt);
		} else if (stmt instanceof CallStatement) {
			return visit((CallStatement) stmt);
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

	protected T visit(CallStatement stmt) {
		return null;
	}

}
