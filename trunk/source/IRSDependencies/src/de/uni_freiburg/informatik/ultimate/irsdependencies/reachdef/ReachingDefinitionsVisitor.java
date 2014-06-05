package de.uni_freiburg.informatik.ultimate.irsdependencies.reachdef;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

public class ReachingDefinitionsVisitor extends BoogieVisitor {

	private ReachingDefinitionsStatementAnnotation mCurrentRD;
	private Statement mCurrentStatement;

	private enum Mode {
		LHS, RHS
	}

	private Mode mMode;

	public ReachingDefinitionsVisitor(ReachingDefinitionsStatementAnnotation current) {
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
			mCurrentRD.addUse(expr.getIdentifier(), mCurrentStatement);
			break;
		}
	}

	private void UpdateDef(String identifier, Statement currentStatement) {
		mCurrentRD.removeAllDefs(identifier);
		mCurrentRD.addDef(identifier, currentStatement);

	}

}
