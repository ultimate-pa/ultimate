/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IType;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * Translates Boogie types into SMT sorts and vice versa.
 * @author Matthias Heizmann
 *
 */
public class TypeSortTranslator {


	protected final Script m_Script;

	private final Map<IType, Sort> m_type2sort = new HashMap<IType, Sort>();
	private final Map<Sort, IType> m_sort2type = new HashMap<Sort, IType>();
	final Map<String, Map<String, Expression[]>> m_Type2Attributes =
			new HashMap<String, Map<String,Expression[]>>();

	private final boolean m_BlackHoleArrays;

	private final IUltimateServiceProvider mServices;

	public TypeSortTranslator(
			Collection<TypeDeclaration> declarations,
			Script script,
			boolean blackHoleArrays, IUltimateServiceProvider services) {
		mServices = services;
		m_BlackHoleArrays = blackHoleArrays;
		m_Script = script;
		{
			// Add type/sort bool to mapping. We need this in our
			// backtranslation in the case where there was no Boolean 
			// variable in the Boogie program but we translate a boolean
			// term e.g., "true".
			Sort boolSort = m_Script.sort("Bool");
			IType boolType = BoogieType.boolType;
			m_type2sort.put(boolType, boolSort);
			m_sort2type.put(boolSort, boolType);
		}
		for (TypeDeclaration typeDecl : declarations) {
			declareType(typeDecl);
		}

	}
	
	public IType getType(Sort sort) {
		IType type = m_sort2type.get(sort);
		if (type == null) {
			//TODO Matthias: The following special treatment of arrays is only
			//necessary if we allow to backtranslate to arrays that do not occur
			//in the boogie program. Might be useful if we allow store
			// expressions in interpolants and don't replace them by select
			// expressions.
			if (sort.isArraySort()) {
				assert sort.getName().equals("Array");
				Sort indexSort = sort.getArguments()[0];
				Sort valueSort = sort.getArguments()[1];
				BoogieType[] indexTypes = { (BoogieType) getType(indexSort) };
				BoogieType valueType = (BoogieType) getType(valueSort);
				type = BoogieType.createArrayType(0, indexTypes, valueType);
			} else {
				throw new IllegalArgumentException("Unknown sort" + sort);
			}
		}
		return type;
	}
	
	
	/**
	 * Return the SMT sort for a boogie type.
	 * If the (type,sort) pair is not already stored in m_type2sort the 
	 * corresponding sort is constructed and the pair (sort, type) is added to
	 * m_sort2type which is used for a backtranslation.
	 * @param BoogieASTNode BoogieASTNode for which Sort is computed 
	 */
	public Sort getSort(IType type, BoogieASTNode BoogieASTNode) {
		if (type instanceof BoogieType) {
			type = ((BoogieType) type).getUnderlyingType();
		}
		if (m_type2sort.containsKey(type)) {
			return m_type2sort.get(type);
		} else {
			return constructSort(type, BoogieASTNode);
		}
	}
	
	
	private void declareType(TypeDeclaration typeDecl) {
		final String[] typeParams = typeDecl.getTypeParams();
		if (typeParams.length != 0) {
			throw new IllegalArgumentException("Only types without parameters supported");
		}
		final String id = typeDecl.getIdentifier();

		final Map<String, Expression[]> attributes = Boogie2SmtSymbolTable.extractAttributes(typeDecl);
		if (attributes != null) {
			m_Type2Attributes.put(id, attributes);
			final String attributeDefinedIdentifier = Boogie2SmtSymbolTable.
					checkForAttributeDefinedIdentifier(attributes, Boogie2SmtSymbolTable.s_BUILTINIDENTIFIER);
			if (attributeDefinedIdentifier != null) {
				// we do not declare or define a Sort since we should use
				// a built-in Sort.
				return;
			}
		}
		if (typeDecl.getSynonym() == null) {
			m_Script.declareSort(id, 0);
		} else {
			Sort synonymSort = getSort(typeDecl.getSynonym().getBoogieType(), typeDecl);
			m_Script.defineSort(id, new Sort[0], synonymSort);
		}
	}
		
		
		
	/**
	 * Construct the SMT sort for a boogie type.
	 * Store the (type, sort) pair in m_type2sort. Store the (sort, type) pair 
	 * in m_sort2type.
	 * @param BoogieASTNode BoogieASTNode for which Sort is computed 
	 */
	protected Sort constructSort(IType boogieType, BoogieASTNode BoogieASTNode) {
		Sort result;
		if (boogieType instanceof PrimitiveType) {
			if (boogieType.equals(PrimitiveType.boolType)) {
				result = m_Script.sort("Bool");
			} else if (boogieType.equals(PrimitiveType.intType)) {
				result = m_Script.sort("Int");
			} else if (boogieType.equals(PrimitiveType.realType)) {
				result = m_Script.sort("Real");
			} else if (boogieType.equals(PrimitiveType.errorType)) {
				throw new IllegalArgumentException("BoogieAST contains type " +
						"errors. This plugin supports only BoogieASTs without type errors");
			} else if (((PrimitiveType) boogieType).getTypeCode() > 0) {
				int bitvectorSize = ((PrimitiveType) boogieType).getTypeCode();
				BigInteger[] sortIndices = { BigInteger.valueOf(bitvectorSize) };
				result = m_Script.sort("BitVec", sortIndices);
			} else {
				throw new IllegalArgumentException("Unsupported PrimitiveType " + boogieType);
			}
		}
		else if (boogieType instanceof ArrayType) {
			ArrayType arrayType = (ArrayType) boogieType;
			Sort rangeSort = constructSort(arrayType.getValueType(), BoogieASTNode);
			if (m_BlackHoleArrays) {
				result = rangeSort;
			} else {
				try {
					for (int i = arrayType.getIndexCount() - 1; i >= 1; i--) {
						Sort sorti = constructSort(arrayType.getIndexType(i), BoogieASTNode);
						rangeSort = m_Script.sort("Array", sorti, rangeSort);
					}
					Sort domainSort = constructSort(arrayType.getIndexType(0), BoogieASTNode);
					result = m_Script.sort("Array", domainSort,rangeSort);
				}
				catch (SMTLIBException e) {
					if (e.getMessage().equals("Sort Array not declared")) {
						Boogie2SMT.reportUnsupportedSyntax(BoogieASTNode, 
								"Solver does not support arrays", mServices);
						throw e;
					}
					else {
						throw new AssertionError(e);
					}
				}
			}
		}
		else if (boogieType instanceof ConstructedType) {
			ConstructedType constructedType = (ConstructedType) boogieType;
			String name = constructedType.getConstr().getName();
			Map<String, Expression[]> attributes = m_Type2Attributes.get(name);
			if (attributes == null) {
				result = m_Script.sort(name);
			} else {
				final String attributeDefinedIdentifier = Boogie2SmtSymbolTable.
						checkForAttributeDefinedIdentifier(attributes, Boogie2SmtSymbolTable.s_BUILTINIDENTIFIER);
				if (attributeDefinedIdentifier == null) {
					result = m_Script.sort(name);
				} else {
					// use SMT identifier that was defined by our "builtin"
					// attribute
					final BigInteger[] indices = Boogie2SmtSymbolTable.checkForIndices(attributes);
					result = m_Script.sort(attributeDefinedIdentifier, indices);
				}
			}
		} else {
			throw new IllegalArgumentException("Unsupported type " + boogieType);
		}
		m_type2sort.put(boogieType, result);
		m_sort2type.put(result, boogieType);
		return result;
	}
	
}
