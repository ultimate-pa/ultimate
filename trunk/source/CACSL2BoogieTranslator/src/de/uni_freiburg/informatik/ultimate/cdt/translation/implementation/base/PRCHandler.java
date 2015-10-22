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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.ArrayHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.PRFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;

public class PRCHandler extends CHandler {
	
    private LinkedHashSet<IASTNode> variablesOnHeap;

    public HashSet<IASTNode> getVarsForHeap() {
    	return variablesOnHeap;
    }	

    ////////////
	
	
	public PRCHandler(Dispatcher main, CACSL2BoogieBacktranslator backtranslator, boolean errorLabelWarning,
			Logger logger, ITypeHandler typeHandler, boolean bitvectorTranslation) {
		super(main, backtranslator, errorLabelWarning, logger, typeHandler, bitvectorTranslation);
		
		variablesOnHeap = new LinkedHashSet<>();

		this.mTypeHandler = typeHandler;

		this.mArrayHandler = new ArrayHandler();
		this.mFunctionHandler = new PRFunctionHandler(m_ExpressionTranslation);
		this.mMemoryHandler = new MemoryHandler(mFunctionHandler, false, mTypeSizeComputer, m_ExpressionTranslation);
		this.mStructHandler = new StructHandler(mMemoryHandler, mTypeSizeComputer, m_ExpressionTranslation);
		this.mSymbolTable = new SymbolTable(main);
		this.mContract = new ArrayList<ACSLNode>();
		this.mCurrentDeclaredTypes = new ArrayDeque<TypesResult>();
	}
	
	@Override
	public Result visit(Dispatcher main, IASTUnaryExpression node) {
		switch (node.getOperator()) {
		case IASTUnaryExpression.op_amper:
			ILocation loc = LocationFactory.createCLocation(node);
			ExpressionResult o = (ExpressionResult) main.dispatch(node.getOperand());
			final RValue ad;
			if (o.lrVal instanceof HeapLValue) {
				ad = new RValue(((HeapLValue) o.lrVal).getAddress(), new CPointer(o.lrVal.getCType()));
//				throw new AssertionError("impossible");
			} else if (o.lrVal instanceof LocalLValue) {
				Expression expr = o.lrVal.getValue();
				if (expr instanceof IdentifierExpression) {
					String id = ((IdentifierExpression) expr).getIdentifier();
					SymbolTable st = main.cHandler.getSymbolTable();
					String cid = st.getCID4BoogieID(id, loc);
					SymbolTableValue value = st.get(cid, loc);
//					CType type = value.getCVariable().getUnderlyingType();
//					if (type instanceof CArray || type instanceof CStruct) {
						((PRCHandler) main.cHandler).getVarsForHeap().add(value.getDeclarationNode());
//					}
				}
				expr.toString();
				ad = new RValue(o.lrVal.getValue(), new CPointer(o.lrVal.getCType()));
			} else if (o.lrVal instanceof RValue) {
				throw new AssertionError("cannot take address of RValue");
			} else {
				throw new AssertionError("Unknown value");
			}
//			
//			//can't really addressof at this point, returning the value instead but wiht pointer type
////			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
//			RValue ad = null;
//			if (o.lrVal instanceof HeapLValue)
//				ad = new RValue(((HeapLValue) o.lrVal).getAddress(), new CPointer(o.lrVal.getCType()));
//			else 
//				ad = new RValue(o.lrVal.getValue(), new CPointer(o.lrVal.getCType()));

			return new ExpressionResult(ad);
			default:
				return super.visit(main, node);
		}
	}
}
