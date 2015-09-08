/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
		
		CType lUlType = left.getCType().getUnderlyingType();
		CType rUlType = right.getCType().getUnderlyingType();

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
