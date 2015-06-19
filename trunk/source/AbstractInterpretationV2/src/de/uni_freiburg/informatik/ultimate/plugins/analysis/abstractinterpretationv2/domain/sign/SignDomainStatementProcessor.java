package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.rmi.activation.UnknownObjectException;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainState.SignDomainValue;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link SignDomainState} for the given Statement.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignDomainStatementProcessor extends BoogieVisitor {

	private SignDomainState mOldState;
	private String mCurrentLhs;
	
	private SignDomainValue mCurrentState;

	public SignDomainState process(SignDomainState oldState, Statement statement) {
		mOldState = oldState;

		processStatement(statement);

		return oldState;
	}

	@Override
	protected void visit(AssignmentStatement statement) {

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();

		for (int i = 0; i < lhs.length; i++) {
			processLeftHandSide(lhs[i]);
			processExpression(rhs[i]);
		}
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mCurrentLhs = lhs.getIdentifier();
	}

	@Override
	protected void visit(RealLiteral expr) {
		// TODO Auto-generated method stub
		super.visit(expr);
	}

	@Override
	protected void visit(IntegerLiteral expr) {
		mCurrentState = processIntegerLiteral(expr.getValue());
	}

	private SignDomainValue processRealLiteral(String realLiteral) {
		BigDecimal number;
		try {
			number = new BigDecimal(realLiteral);
		} catch (NumberFormatException e) {
			throw new UnsupportedOperationException("The real number string " + realLiteral
			        + " cannot be transformed to a numerical representation.");
		}

		int num = number.signum();

		return EvaluateNumber(num);
	}

	private SignDomainValue processIntegerLiteral(String intLiteral) {
		BigInteger number;
		try {
			number = new BigInteger(intLiteral);
		} catch (NumberFormatException e) {
			throw new UnsupportedOperationException("The integer string " + intLiteral
			        + " cannot be transformed to a numerical representation.");
		}

		int num = number.signum();

		return EvaluateNumber(num);
	}

	private SignDomainValue EvaluateNumber(int num) {
		if (num > 0) {
			return SignDomainValue.POSITIVE;
		}

		if (num < 0) {
			return SignDomainValue.NEGATIVE;
		}

		return SignDomainValue.ZERO;
	}
}
