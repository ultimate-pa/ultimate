package de.uni_freiburg.informatik.ultimate.source.java.joogie;

import java.util.List;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;
import org.joogie.boogie.constants.RealConstant;
import org.joogie.boogie.constants.TypeExpression;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.IteExpression;
import org.joogie.boogie.expressions.QuantifiedExpression;
import org.joogie.boogie.expressions.QuantifiedExpression.Quantifier;
import org.joogie.boogie.expressions.SimpleHeapAccess;
import org.joogie.boogie.expressions.Variable;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExpressionTranslator extends JoogieExpressionTransformer<Expression> {

	// TODO: Why is a Variable an expression in Joogie?

	private final Logger mLogger;
	private final Expression mExpression;
	private final ILocation mLocation;

	private ExpressionTranslator(final Logger logger, final ILocation location,
			org.joogie.boogie.expressions.Expression expression) {
		mLogger = logger;
		mLocation = location;
		mExpression = visit(expression);
	}

	private Expression getTranslation() {
		return mExpression;
	}

	public static Expression translate(final Logger logger, final ILocation location,
			org.joogie.boogie.expressions.Expression expression) {
		return new ExpressionTranslator(logger, location, expression).getTranslation();
	}

	@Override
	protected Expression visit(final Variable expr) {
		return new IdentifierExpression(mLocation, expr.getName());
	}

	@Override
	protected Expression visit(final RealConstant expr) {
		return new RealLiteral(mLocation, expr.toBoogie());
	}

	@Override
	protected Expression visit(final UboundedIntConstant expr) {
		return new IntegerLiteral(mLocation, expr.toBoogie());
	}

	@Override
	protected Expression visit(final ArrayReadExpression expr) {
		return new ArrayAccessExpression(mLocation, visit(expr.getBaseExpression()),
				new Expression[] { visit(expr.getIndexExpression()) });
	}

	@Override
	protected Expression visit(final SimpleHeapAccess expr) {
		return new ArrayAccessExpression(mLocation, visit(expr.getHeapVariable()),
				new Expression[] { visit(expr.getBaseExpression()), visit(expr.getFieldExpression()) });
	}

	@Override
	protected Expression visit(final TypeExpression expr) {
		return new IdentifierExpression(mLocation, expr.getTypeVariable().getName());
	}

	@Override
	protected Expression visit(final InvokeExpression expr) {
		assert expr.getModifiedVars() == null
				|| expr.getModifiedVars().isEmpty() : "expressions must be side-effect free";
		return new FunctionApplication(mLocation, expr.getInvokedProcedure().getName(), expr.getArguments().stream()
				.map(arg -> visit(arg)).collect(Collectors.toList()).toArray(new Expression[0]));
	}

	@Override
	protected Expression visit(final BinOpExpression expr) {
		final Operator operator;

		switch (expr.getOp()) {
		case Div:
			operator = Operator.ARITHDIV;
			break;
		case Eq:
			operator = Operator.COMPEQ;
			break;
		case Ge:
			operator = Operator.COMPGEQ;
			break;
		case Gt:
			operator = Operator.COMPGT;
			break;
		case Implies:
			operator = Operator.LOGICIMPLIES;
			break;
		case LAnd:
			operator = Operator.LOGICAND;
			break;
		case LOr:
			operator = Operator.LOGICOR;
			break;
		case Le:
			operator = Operator.COMPLEQ;
			break;
		case Lt:
			operator = Operator.COMPLT;
			break;
		case Minus:
			operator = Operator.ARITHMINUS;
			break;
		case Mul:
			operator = Operator.ARITHMUL;
			break;
		case Neq:
			operator = Operator.COMPNEQ;
			break;
		case Plus:
			operator = Operator.ARITHPLUS;
			break;
		default:
			throw new UnsupportedOperationException("Unknown Binop " + expr.getOp());
		}
		return new BinaryExpression(mLocation, operator, visit(expr.getLhs()), visit(expr.getRhs()));
	}

	@Override
	protected Expression visit(final IteExpression expr) {
		return new IfThenElseExpression(mLocation, visit(expr.getCond()), visit(expr.getThen()), visit(expr.getElse()));
	}

	@Override
	protected Expression visit(final QuantifiedExpression expr) {
		final List<VarList> parameters = expr.getBoundVariables().stream().map(bv -> new VarList(mLocation,
				new String[] { bv.getName() }, TypeTranslator.translate(bv, mLocation)))
				.collect(Collectors.toList());
		return new QuantifierExpression(mLocation, expr.getQuantifier() == Quantifier.ForAll, new String[0],
				parameters.toArray(new VarList[parameters.size()]), new Attribute[0], visit(expr.getExpression()));
	}

	@Override
	protected Expression visit(final org.joogie.boogie.expressions.UnaryExpression expr) {
		final UnaryExpression.Operator op;
		switch (expr.getOperator()) {
		case Minus:
			op = UnaryExpression.Operator.ARITHNEGATIVE;
			break;
		case Not:
			op = UnaryExpression.Operator.LOGICNEG;
			break;
		default:
			throw new UnsupportedOperationException("Unknown unary operator " + expr.getOperator());
		}
		return new UnaryExpression(mLocation, op, visit(expr.getExpression()));
	}
}
