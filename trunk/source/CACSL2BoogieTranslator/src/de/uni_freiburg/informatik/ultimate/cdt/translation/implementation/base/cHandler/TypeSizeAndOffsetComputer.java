/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Class that is used to compute the bytesize (what that is returned by the
 * sizeof operator) of types and the memory offsets for fields of structs.
 * @author Matthias Heizmann
 */
public class TypeSizeAndOffsetComputer {
		
		/**
	     * A set of constants, required for the memory model. E.g. sizeof and offset
	     * constants.
	     */
	    private final LinkedHashSet<ConstDeclaration> m_Constants;
	    /**
	     * A set of axioms, required for the memory model. E.g. for sizeof and
	     * offset constants.
	     */
	    private final LinkedHashSet<Axiom> m_Axioms;
		
	    private final HashMap<CType, SizeTValue> m_TypeSizeCache;
	    private final HashMap<CStruct, Expression[]> m_StructOffsets;
	    private final TypeHandler m_TypeHandler;
	    
		private final TypeSizes m_TypeSizes;
		

		private final AExpressionTranslation m_ExpressionTranslation;
		
		/**
		 * Given the field of a struct myStruct.myField such that the offset
		 * of the field is n, the computation can
		 * <ul>  
		 * <li> return the number n or
		 * <li> return a constant #offset~myStruct~myField and add an axiom
		 *     #offset~myStruct~myField == 4
		 * </ul>
		 * If false we do the first, if true we do the latter.
		 */
		private final boolean m_PreferConstantsOverValues = false;
		
	    private SizeTValue m_TypeSizePointer = null;
	    
	    public TypeSizeAndOffsetComputer(TypeHandler typeHandler, AExpressionTranslation expressionTranslation, TypeSizes typeSizes) {
			m_ExpressionTranslation = expressionTranslation;
	    	m_TypeHandler = typeHandler;
	    	m_TypeSizes = typeSizes;
	    	m_TypeSizeCache = new HashMap<>();
	    	m_StructOffsets = new HashMap<>();
	    	m_Constants = new LinkedHashSet<>();
	    	m_Axioms = new LinkedHashSet<>();
		}
	    
	    /**
	     * @return An Expression that represents the size (in bytes) of the
	     * given CType. If needed additional constant declarations and axioms
	     * are constructed. The additional constant declarations and axioms
	     * can be obtained using the {@link TypeSizeAndOffsetComputer#getConstants()} 
	     * and {@link TypeSizeAndOffsetComputer#getAxioms()} methods.
	     */
	    public Expression constructBytesizeExpression(ILocation loc, CType cType) {
	    	SizeTValue value = computeSize(loc, cType);
	    	return value.asExpression(loc);
	    }
	    
	    /**
	     * @return An Expression that represents the offset (in bytes) at which
	     * a certain field of a stuct is stored (on the heap). 
	     */
	    public Expression constructOffsetForField(ILocation loc, CStruct cStruct, int fieldIndex) {
	    	if (!m_TypeSizeCache.containsKey(cStruct)) {
	    		assert !m_StructOffsets.containsKey(cStruct) : "both or none";
	    		computeSize(loc, cStruct);
	    	}
	    	Expression[] offsets = m_StructOffsets.get(cStruct);
	    	assert offsets.length == cStruct.getFieldCount() : "inconsistent struct";
	    	return offsets[fieldIndex];
	    }
	    
	    public Expression constructOffsetForField(ILocation loc, CStruct cStruct, String fieldId) {
	    	int fieldIndex = Arrays.asList(cStruct.getFieldIds()).indexOf(fieldId);
	    	return constructOffsetForField(loc, cStruct, fieldIndex);
	    }
	    
	    private Expression constructTypeSizeConstant(ILocation loc, CType cType) {
	    	String id = SFO.SIZEOF + cType.toString();
	    	declareConstant(loc, id);
	    	IdentifierExpression idexpr = new IdentifierExpression(loc, id);
	    	return idexpr;
	    }
	    
	    private Expression constructTypeSizeConstant_Pointer(ILocation loc) {
	    	String id = SFO.SIZEOF + SFO.POINTER;
	    	declareConstant(loc, id);
	    	IdentifierExpression idexpr = new IdentifierExpression(loc, id);
	    	return idexpr;
	    }
	    
	    /**
	     * Construct Expression that represents the field of a struct or union. 
	     */
	    private Expression constructTypeSizeConstantForStructField(ILocation loc, 
	    			CStruct cStruct, int fieldNumber) {
				String fieldId = cStruct.getFieldIds()[fieldNumber];	
				String resultId = SFO.OFFSET + cStruct.toString() + "~" + fieldId;
				declareConstant(loc, resultId);
				Expression result = new IdentifierExpression(loc, resultId);
				return result;
	    }
	    
	    private void declareConstant(ILocation loc, String id) {
	    	ASTType astType =  m_TypeHandler.ctype2asttype(loc, getSize_T());
	    	VarList varList = new VarList(loc, new String[] { id }, astType);
	    	ConstDeclaration decl = new ConstDeclaration(loc, 
	    			new Attribute[0], false, varList, null, false);
			m_Constants.add(decl);
	    }

		private SizeTValue computeSize(ILocation loc, CType cType) {
			CType underlyingType = cType.getUnderlyingType();
			if (underlyingType instanceof CPointer) {
				if (m_TypeSizePointer == null) {
					m_TypeSizePointer = constructSizeTValue_Pointer(loc);
				}
				return m_TypeSizePointer;
			} else if (underlyingType instanceof CEnum) { 
				// an Enum contains constants of type int
				return computeSize(loc, new CPrimitive(PRIMITIVE.INT));
			} else {
				SizeTValue sizeTValue = m_TypeSizeCache.get(underlyingType);
				if (sizeTValue == null) {
					if (underlyingType instanceof CPrimitive) {
						sizeTValue = constructSizeTValue_Primitive(loc, (CPrimitive) underlyingType);
					} else if (underlyingType instanceof CArray) {
						sizeTValue = constructSizeTValue_Array(loc, (CArray) underlyingType);
					} else if (underlyingType instanceof CStruct) {
						sizeTValue = constructSizeTValueAndOffsets_StructAndUnion(loc, (CStruct) underlyingType);
					} else {
						throw new UnsupportedOperationException("Unsupported type" + underlyingType);
					}
					m_TypeSizeCache.put(underlyingType, sizeTValue);
				} 
				return sizeTValue;
			}
	    }
		
		private SizeTValue constructSizeTValue_Primitive(ILocation loc, CPrimitive cPrimitive) {
			final SizeTValue result;
			if (m_TypeSizes.useFixedTypeSizes()) {
				int size = m_TypeSizes.getSize(cPrimitive.getType());
				result = new SizeTValue_Integer(BigInteger.valueOf(size));
			} else {
				Expression sizeConstant = constructTypeSizeConstant(loc, cPrimitive);
				result = new SizeTValue_Expression(sizeConstant);
				Axiom axiom = constructNonNegativeAxiom(loc, sizeConstant);
				m_Axioms.add(axiom);
			}
			return result;
		}
		
		private SizeTValue constructSizeTValue_Array(ILocation loc, CArray cArray) {
			List<SizeTValue> factors = new ArrayList<>();
			SizeTValue valueSize = computeSize(loc, cArray.getValueType());
			factors.add(valueSize);
			for (RValue dim : cArray.getDimensions()) {
				SizeTValue dimSize = extractSizeTValue(dim);
				factors.add(dimSize);
			}
			SizeTValue size = (new SizeTValueAggregator_Multiply()).aggregate(loc, factors);
			final SizeTValue result;
			if (m_PreferConstantsOverValues) {
				Expression sizeConstant = constructTypeSizeConstant(loc, cArray);
				result = new SizeTValue_Expression(sizeConstant);
				Expression equality = m_ExpressionTranslation.constructBinaryComparisonExpression(
						loc, IASTBinaryExpression.op_equals, sizeConstant, getSize_T(), 
						size.asExpression(loc), getSize_T());
				Axiom axiom = new Axiom(loc, new Attribute[0], equality);
				m_Axioms.add(axiom);
			} else {
				result = size;
			}
			return result;
		}
		
		private SizeTValue constructSizeTValueAndOffsets_StructAndUnion(ILocation loc, CStruct cStruct) {
 			if (cStruct.isIncomplete()) {
 				// according to C11 6.5.3.4.1
 				throw new IllegalArgumentException("cannot determine size of incomplete type");
 			}
 			if (m_StructOffsets.containsKey(cStruct)) {
 				throw new AssertionError("must not be computed");
 			}
 			Expression[] offsets = new Expression[cStruct.getFieldCount()];
 			m_StructOffsets.put(cStruct, offsets);
 			List<SizeTValue> fieldTypeSizes = new ArrayList<>();
 			for (int i = 0; i < cStruct.getFieldCount(); i++) {
 				CType fieldType = cStruct.getFieldTypes()[i];

 				final Expression offset;
 				if (cStruct instanceof CUnion) {
 					offset = m_ExpressionTranslation.constructLiteralForIntegerType(loc, getSize_T(), BigInteger.ZERO);
 				} else {
 					SizeTValue sumOfPreceedingFields = (new SizeTValueAggregator_Add()).aggregate(loc, fieldTypeSizes);
 					offset = sumOfPreceedingFields.asExpression(loc);
 				}
 				
 				if (m_PreferConstantsOverValues) {
 					Expression fieldConstant = constructTypeSizeConstantForStructField(loc, cStruct, i);
 					Expression equality = m_ExpressionTranslation.constructBinaryComparisonExpression(
 							loc, IASTBinaryExpression.op_equals, fieldConstant, getSize_T(), 
 							offset, getSize_T());
 					Axiom axiom = new Axiom(loc, new Attribute[0], equality);
 					m_Axioms.add(axiom);
 					offsets[i] = fieldConstant;
 				} else {
 					offsets[i] = offset;
 				}
 				SizeTValue fieldTypeSize = computeSize(loc, fieldType);
 				fieldTypeSizes.add(fieldTypeSize);
 			}
 			
 			final SizeTValueAggregator aggregator;
 			if (cStruct instanceof CUnion) {
 				aggregator = new SizeTValueAggregator_Max();
 			} else {
 				aggregator = new SizeTValueAggregator_Add();
 			}
 			return aggregator.aggregate(loc, fieldTypeSizes);
		}
		
		private SizeTValue constructSizeTValue_Pointer(ILocation loc) {
			final SizeTValue result;
			if (m_TypeSizes.useFixedTypeSizes()) {
				int size = m_TypeSizes.getSizeOfPointer();
				result = new SizeTValue_Integer(BigInteger.valueOf(size));
			} else {
				Expression sizeConstant = constructTypeSizeConstant_Pointer(loc);
				result = new SizeTValue_Expression(sizeConstant);
				Axiom axiom = constructNonNegativeAxiom(loc, sizeConstant);
				m_Axioms.add(axiom);
			}
			return result;
		}

		private Axiom constructNonNegativeAxiom(ILocation loc, Expression sizeConstant) {
			Expression zero = m_ExpressionTranslation.constructLiteralForIntegerType(
					loc, getSize_T(), BigInteger.ZERO);
			Expression isNonNegative = m_ExpressionTranslation.constructBinaryComparisonExpression(
					loc, IASTBinaryExpression.op_greaterEqual, sizeConstant, getSize_T(), 
					zero, getSize_T());
			Axiom axiom = new Axiom(loc, new Attribute[0], isNonNegative);
			return axiom;
		}
		
		private SizeTValue extractSizeTValue(RValue rvalue) {
			final BigInteger value = m_ExpressionTranslation.extractIntegerValue(rvalue);
			if (value != null) {
				return new SizeTValue_Integer(value);
			} else {
				return new SizeTValue_Expression(rvalue.getValue());
			}
		}

		private abstract class SizeTValueAggregator {
			
			public SizeTValue aggregate(ILocation loc, List<SizeTValue> values) {
				if (values.isEmpty()) {
					return new SizeTValue_Integer(resultForZeroOperandCase());
				}
				LinkedList<SizeTValue> tmpValues = new LinkedList<>(values); 
				BigInteger aggregatedIntegers = null;
				Iterator<SizeTValue> it = tmpValues.iterator();
				while (it.hasNext()) {
					SizeTValue current = it.next();
					if (current instanceof SizeTValue_Integer) {
						BigInteger currentInteger = ((SizeTValue_Integer) current).getInteger();
						if (aggregatedIntegers == null) {
							aggregatedIntegers = currentInteger;
						} else {
							aggregatedIntegers = aggregateIntegers(aggregatedIntegers, currentInteger);
						}
						it.remove();
					}
				}
				if (tmpValues.isEmpty()) {
					return new SizeTValue_Integer(aggregatedIntegers);
				} else {
					if (aggregatedIntegers != null) {
						tmpValues.add(new SizeTValue_Integer(aggregatedIntegers));
					}
					if (tmpValues.size() == 1) {
						return tmpValues.getFirst();
					} else {
						return aggregateExpressions(loc, tmpValues);
					}
				}
			}

			private SizeTValue aggregateExpressions(ILocation loc, LinkedList<SizeTValue> values) {
				assert !values.isEmpty() : "at least one needed";
				SizeTValue first = values.removeFirst();
				Expression aggregatedExpressions = first.asExpression(loc);
				for (SizeTValue value : values) {
					Expression expr = value.asExpression(loc);
					aggregatedExpressions = aggregateExpressions(loc, aggregatedExpressions, expr);
				}
				return new SizeTValue_Expression(aggregatedExpressions);
			}

			protected abstract Expression aggregateExpressions(ILocation loc, Expression op1, Expression op2);
			protected abstract BigInteger aggregateIntegers(BigInteger op1, BigInteger op2);
			protected abstract BigInteger resultForZeroOperandCase();
		}
		
		private class SizeTValueAggregator_Add extends SizeTValueAggregator {

			@Override
			protected Expression aggregateExpressions(ILocation loc, Expression op1, Expression op2) {
				return m_ExpressionTranslation.constructArithmeticExpression(
						loc, IASTBinaryExpression.op_plus, op1, 
						getSize_T(), op2, getSize_T());
			}

			@Override
			protected BigInteger aggregateIntegers(BigInteger op1, BigInteger op2) {
				return op1.add(op2);
			}

			@Override
			protected BigInteger resultForZeroOperandCase() {
				return BigInteger.ZERO;
			}
		}
		
		private class SizeTValueAggregator_Multiply extends SizeTValueAggregator {

			@Override
			protected Expression aggregateExpressions(ILocation loc, Expression op1, Expression op2) {
				return m_ExpressionTranslation.constructArithmeticExpression(
						loc, IASTBinaryExpression.op_multiply, op1, 
						getSize_T(), op2, getSize_T());
			}

			@Override
			protected BigInteger aggregateIntegers(BigInteger op1, BigInteger op2) {
				return op1.multiply(op2);
			}

			@Override
			protected BigInteger resultForZeroOperandCase() {
				return BigInteger.ONE;
			}
		}
		
		
		private class SizeTValueAggregator_Max extends SizeTValueAggregator {

			@Override
			protected Expression aggregateExpressions(ILocation loc, Expression op1, Expression op2) {
				Expression firstIsGreater = m_ExpressionTranslation.constructBinaryComparisonExpression(
						loc, IASTBinaryExpression.op_greaterEqual, 
						op1, getSize_T(), op2, getSize_T());
				Expression result = new IfThenElseExpression(loc, firstIsGreater, op1, op2);
				return result;
			}

			@Override
			protected BigInteger aggregateIntegers(BigInteger op1, BigInteger op2) {
				return op1.max(op2);
			}

			@Override
			protected BigInteger resultForZeroOperandCase() {
				return BigInteger.ZERO;
			}
		}
	    
		private abstract class SizeTValue {
	    	public abstract Expression asExpression(ILocation loc);
	    }
	    
	    private class SizeTValue_Integer extends SizeTValue {
	    	private final BigInteger m_Value;

			public SizeTValue_Integer(BigInteger value) {
				this.m_Value = value;
			}
			
			public Expression asExpression(ILocation loc) {
				return m_ExpressionTranslation.constructLiteralForIntegerType(loc, getSize_T(), m_Value);
			}
			public BigInteger getInteger() {
				return m_Value;
			}
			@Override
			public String toString() {
				return String.valueOf(m_Value);
			}
	    }
	    
	    private class SizeTValue_Expression extends SizeTValue {
	    	private final Expression m_Value;

			public SizeTValue_Expression(Expression value) {
				this.m_Value = value;
			}
			public Expression asExpression(ILocation loc) {
				return this.m_Value;
			}
			@Override
			public String toString() {
				return String.valueOf(m_Value);
			}
	    }
	    
		/**
		 * Get the CType that represents <em> size_t </em>.
		 * TODO: Currently hard-coded to int. Should probably be a setting.
		 * This is unsound, but in the integer translation more efficient than 
		 * uint (no wraparound). 
		 * TODO: maybe this class is not the right place. 
		 */
		public CPrimitive getSize_T() {
			return new CPrimitive(PRIMITIVE.INT);
		}

		public LinkedHashSet<ConstDeclaration> getConstants() {
			return m_Constants;
		}

		public LinkedHashSet<Axiom> getAxioms() {
			return m_Axioms;
		}
		
		
	}