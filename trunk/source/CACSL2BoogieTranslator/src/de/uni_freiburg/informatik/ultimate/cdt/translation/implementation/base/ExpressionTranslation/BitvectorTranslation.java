package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizeConstants;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class BitvectorTranslation extends AbstractExpressionTranslation {

	public BitvectorTranslation(TypeSizeConstants m_TypeSizeConstants) {
		super(m_TypeSizeConstants);
	}

	@Override
	public ResultExpression literalTranslation(Dispatcher main, IASTLiteralExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_char_constant:
		{
			String val = ISOIEC9899TC3.handleCharConstant(new String(node.getValue()), loc, main);
			CPrimitive cprimitive = new CPrimitive(PRIMITIVE.CHAR);
			int bitlength = 8 * m_TypeSizeConstants.getCPrimitiveToTypeSizeConstant().get(cprimitive);
			return new ResultExpression(new RValue(new BitvecLiteral(loc, val, bitlength), cprimitive));
		}
		case IASTLiteralExpression.lk_integer_constant:
		{
			String val = new String(node.getValue());
			RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, main, true, m_TypeSizeConstants);
			return new ResultExpression(rVal);
		}
		default:
			return super.literalTranslation(main, node);
		}
	}
}
