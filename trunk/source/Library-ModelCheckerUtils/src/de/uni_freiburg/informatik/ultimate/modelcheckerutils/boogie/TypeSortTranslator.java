package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;

/**
 * Translates Boogie types into SMT sorts and vice versa.
 * @author Matthias Heizmann
 *
 */
public class TypeSortTranslator {


	private final Script m_Script;

	private final Map<IType, Sort> m_type2sort = new HashMap<IType, Sort>();
	private final Map<Sort, IType> m_sort2type = new HashMap<Sort, IType>();

	private final boolean m_BlackHoleArrays;

	private final IUltimateServiceProvider mServices;

	public TypeSortTranslator(
			Collection<TypeDeclaration> declarations,
			Script script,
			boolean blackHoleArrays, IUltimateServiceProvider services) {
		mServices = services;
		m_BlackHoleArrays = blackHoleArrays;
		m_Script = script;

		Sort boolSort = m_Script.sort("Bool");
		IType boolType = BoogieType.boolType;
		m_type2sort.put(boolType, boolSort);
		m_sort2type.put(boolSort, boolType);
		Sort intSort = m_Script.sort("Int");
		IType intType = BoogieType.intType;
		m_type2sort.put(intType, intSort);
		m_sort2type.put(intSort, intType);
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
		if (m_type2sort.containsKey(type)) {
			return m_type2sort.get(type);
		} else {
			return constructSort(type, BoogieASTNode);
		}
	}
	
	
	private void declareType(TypeDeclaration typeDecl) {
		String id = typeDecl.getIdentifier();
		String[] typeParams = typeDecl.getTypeParams();
		if (typeParams.length != 0) {
			throw new IllegalArgumentException("Only types without parameters supported");
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
	private Sort constructSort(IType boogieType, BoogieASTNode BoogieASTNode) {
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
						Boogie2SMT.reportUnsupportedSyntax(BoogieASTNode, "Solver does not support arrays", mServices);
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
			result = m_Script.sort(name);
		} else {
			throw new IllegalArgumentException("Unsupported type " + boogieType);
		}
		m_type2sort.put(boogieType, result);
		m_sort2type.put(result, boogieType);
		return result;
	}
	
}
