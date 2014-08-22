package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;

public class ReachDefBoogieVisitor extends BoogieVisitor {

	private ReachDefStatementAnnotation mCurrentRD;
	private Statement mCurrentStatement;

	private boolean mIsLHS;
	private boolean mIsAssume;
	private ReachDefStatementAnnotation mOldRD;
	private ScopedBoogieVarBuilder mBuilder;

	public ReachDefBoogieVisitor(ReachDefStatementAnnotation current, ScopedBoogieVarBuilder builder) {
		assert current != null;
		mCurrentRD = current;
		mBuilder = builder;
	}

	public void process(Statement node) throws Throwable {
		assert node != null;
		assert mCurrentRD != null;
		mCurrentStatement = node;
		mIsLHS = false;
		mIsAssume = false;
		mOldRD = (ReachDefStatementAnnotation) mCurrentRD.clone();
		processStatement(node);
	}

	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		// TODO: Problem: how do we recognize array recursion?
		mIsLHS = true;
		LeftHandSide rtr = super.processLeftHandSide(lhs);
		mIsLHS = false;
		return rtr;
	}

	@Override
	protected void visit(VariableLHS lhs) {
		super.visit(lhs);
		UpdateDef(mBuilder.getScopedBoogieVar(lhs), mCurrentStatement);
	}

	@Override
	protected Statement processStatement(Statement statement) {
		mIsAssume = statement instanceof AssumeStatement;
		return super.processStatement(statement);
	}

	@Override
	protected void visit(IdentifierExpression identifier) {
		super.visit(identifier);

		ScopedBoogieVar current = mBuilder.getScopedBoogieVar(identifier);

		if (mIsAssume) {
			// if we are inside an assume, every identifier expression is a use
			// and a def
			UpdateUse(current);
			UpdateDef(current, mCurrentStatement);

		} else {
			// if we are not inside an assume, it depends on the side we are on
			if (mIsLHS) {
				UpdateDef(current, mCurrentStatement);
			} else {
				UpdateUse(current);
			}
		}
	}

	private void UpdateDef(ScopedBoogieVar identifier, Statement currentStatement) {
		mCurrentRD.removeAllDefs(identifier);
		mCurrentRD.addDef(identifier, currentStatement);
	}

	private void UpdateUse(ScopedBoogieVar id) {
		Collection<Statement> stmts = mOldRD.getDef(id);
		if (stmts != null) {
			for (Statement stmt : stmts) {
				mCurrentRD.addUse(id, stmt);
			}
		}
	}

}
