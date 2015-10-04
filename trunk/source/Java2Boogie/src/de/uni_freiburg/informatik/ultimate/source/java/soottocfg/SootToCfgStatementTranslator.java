package de.uni_freiburg.informatik.ultimate.source.java.soottocfg;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SootToCfgStatementTranslator extends SootToCfgStatementTransformer<Statement> {
	private final Logger mLogger;
	private final ILocation mLocation;
	private final Statement mStatement;

	private SootToCfgStatementTranslator(final Logger logger, final ILocation location,
			final soottocfg.cfg.statement.Statement stmt) {
		mLogger = logger;
		mLocation = location;
		mStatement = visit(stmt);
	}

	private Statement getTranslation() {
		return mStatement;
	}

	public static Statement translate(final Logger logger, final ILocation location,
			final soottocfg.cfg.statement.Statement stmt) {
		return new SootToCfgStatementTranslator(logger, location, stmt).getTranslation();
	}

	@Override
	protected Statement visit(soottocfg.cfg.statement.AssertStatement stmt) {
		// TODO Auto-generated method stub
		return super.visit(stmt);
	}

	@Override
	protected Statement visit(soottocfg.cfg.statement.AssignStatement stmt) {
		// TODO Auto-generated method stub
		return super.visit(stmt);
	}

	@Override
	protected Statement visit(soottocfg.cfg.statement.AssumeStatement stmt) {
		// TODO Auto-generated method stub
		return super.visit(stmt);
	}

	@Override
	protected Statement visit(soottocfg.cfg.statement.CallStatement stmt) {
		// TODO Auto-generated method stub
		return super.visit(stmt);
	}
}
