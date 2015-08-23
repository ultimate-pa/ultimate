package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class CastAndConversionHandler {

	
	public static void doPrimitiveVsPointerConversions(Dispatcher main, ILocation loc, MemoryHandler memoryHandler, 
			ResultExpression leftRex, ResultExpression rightRex) {
		RValue left = (RValue) leftRex.lrVal;
		RValue right = (RValue) rightRex.lrVal;
		
		CType lUlType = left.cType.getUnderlyingType();
		CType rUlType = right.cType.getUnderlyingType();

		//save some time if the types are equal..
		if (lUlType.equals(rUlType))
			return; 

		if (lUlType instanceof CPrimitive && rUlType instanceof CPointer
				|| rUlType instanceof CPrimitive && lUlType instanceof CPointer) {
			if (lUlType instanceof CPrimitive) {
				if (left.getValue() instanceof IntegerLiteral
						&& ((IntegerLiteral) left.getValue()).getValue().equals("0")) {
					leftRex.lrVal = new RValue(new IdentifierExpression(loc, SFO.NULL), 
							new CPointer(new CPrimitive(PRIMITIVE.VOID)));
				}
			}
			if (rUlType instanceof CPrimitive) {
				if (right.getValue() instanceof IntegerLiteral
						&& ((IntegerLiteral) right.getValue()).getValue().equals("0")) {
					rightRex.lrVal = new RValue(new IdentifierExpression(loc, SFO.NULL), 
							new CPointer(new CPrimitive(PRIMITIVE.VOID)));
				}

			}
		}
	}
	
}
