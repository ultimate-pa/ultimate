package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;

public class ReachDefBoogieVisitor extends BoogieVisitor {

	private ReachDefStatementAnnotation mCurrentRD;
	private Statement mCurrentStatement;

	private enum Mode {
		LHS, RHS
	}

	private Mode mMode;

	public ReachDefBoogieVisitor(ReachDefStatementAnnotation current) {
		assert current != null;
		mCurrentRD = current;
	}

	public void process(Statement node) throws Throwable {
		assert node != null;
		assert mCurrentRD != null;
		mCurrentStatement = node;
		mMode = Mode.RHS;
		processStatement(node);
	}

	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		mMode = Mode.LHS;
		LeftHandSide rtr = super.processLeftHandSide(lhs);
		mMode = Mode.RHS;
		return rtr;
	}

	@Override
	protected void visit(VariableLHS lhs) {
		super.visit(lhs);
		UpdateDef(lhs.getIdentifier(), mCurrentStatement);
	}

	@Override
	protected void visit(IdentifierExpression expr) {
		super.visit(expr);
		switch (mMode) {
		case LHS:
			UpdateDef(expr.getIdentifier(), mCurrentStatement);
			break;
		case RHS:
			String id = expr.getIdentifier();
			Collection<Statement> stmts = mCurrentRD.getDef(id);
			if (stmts != null) {
				for (Statement stmt : mCurrentRD.getDef(id)) {
					mCurrentRD.addUse(id, stmt);
				}
			}

			break;
		}
	}

	private void UpdateDef(String identifier, Statement currentStatement) {
		mCurrentRD.removeAllDefs(identifier);
		mCurrentRD.addDef(identifier, currentStatement);

	}

}
