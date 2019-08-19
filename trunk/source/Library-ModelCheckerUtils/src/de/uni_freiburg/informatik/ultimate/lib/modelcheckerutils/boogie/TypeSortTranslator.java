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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Translates Boogie types into SMT sorts and vice versa.
 *
 * @author Matthias Heizmann
 *
 */
public class TypeSortTranslator {

	protected final Script mScript;

	private final Map<IBoogieType, Sort> mType2Sort = new HashMap<>();
	private final Map<Sort, IBoogieType> mSort2Type = new HashMap<>();
	private final Map<String, Map<String, Expression[]>> mType2Attributes;
	private final IUltimateServiceProvider mServices;

	public TypeSortTranslator(final Collection<TypeDeclaration> declarations, final Script script,
			final IUltimateServiceProvider services) {
		mType2Attributes = new HashMap<>();
		mServices = services;
		mScript = script;
		{
			// Add type/sort bool to mapping. We need this in our
			// backtranslation in the case where there was no Boolean
			// variable in the Boogie program but we translate a boolean
			// term e.g., "true".
			final Sort boolSort = SmtSortUtils.getBoolSort(mScript);
			final IBoogieType boolType = BoogieType.TYPE_BOOL;
			cacheSort(boolType, boolSort);
		}
		for (final TypeDeclaration typeDecl : declarations) {
			declareType(typeDecl);
		}
	}

	/**
	 * Constructor for ChcToBoogieTranslation. All sort-type pairs are passed as a HashRelation.
	 *
	 * @param sortToType
	 * @param script
	 * @param services
	 */
	public TypeSortTranslator(final HashRelation<Sort, IBoogieType> sortToType, final Script script,
			final IUltimateServiceProvider services) {
		mType2Attributes = new HashMap<>();
		mServices = services;
		mScript = script;
		// {
		// // Add type/sort bool to mapping. We need this in our
		// // backtranslation in the case where there was no Boolean
		// // variable in the Boogie program but we translate a boolean
		// // term e.g., "true".
		// final Sort boolSort = SmtSortUtils.getBoolSort(mScript);
		// final IBoogieType boolType = BoogieType.TYPE_BOOL;
		// cacheSort(boolType, boolSort);
		// }
		for (final Entry<Sort, IBoogieType> en : sortToType.entrySet()) {
			cacheSort(en.getValue(), en.getKey());
		}
	}

	/**
	 * Constructor is only used in a workaround for the backtranslation while dumping path programs.
	 */
	public TypeSortTranslator(final Script script, final IUltimateServiceProvider services) {
		this(Collections.emptySet(), script, services);
		{
			// Add type/sort mapping for Int.
			final Sort intSort = SmtSortUtils.getIntSort(mScript);
			final IBoogieType boolType = BoogieType.TYPE_INT;
			cacheSort(boolType, intSort);
		}
	}

	public IBoogieType getType(final Sort sort) {
		IBoogieType type = mSort2Type.get(sort);
		if (type == null) {
			// TODO Matthias: The following special treatment of arrays is only
			// necessary if we allow to backtranslate to arrays that do not occur
			// in the boogie program. Might be useful if we allow store
			// expressions in interpolants and don't replace them by select
			// expressions.
			if (sort.isArraySort()) {
				assert SmtSortUtils.isArraySort(sort);
				final Sort indexSort = sort.getArguments()[0];
				final Sort valueSort = sort.getArguments()[1];
				final BoogieType[] indexTypes = { (BoogieType) getType(indexSort) };
				final BoogieType valueType = (BoogieType) getType(valueSort);
				type = BoogieType.createArrayType(0, indexTypes, valueType);
			} else if (SmtSortUtils.isBitvecSort(sort)) {
				final BigInteger bvsize = sort.getIndices()[0];
				type = BoogieType.createBitvectorType(bvsize.intValueExact());
				return type;
			} else {
				throw new IllegalArgumentException("Unknown sort " + sort);
			}
		}
		return type;
	}

	/**
	 * Return the SMT sort for a boogie type. If the (type,sort) pair is not already stored in mtype2sort the
	 * corresponding sort is constructed and the pair (sort, type) is added to msort2type which is used for a
	 * backtranslation.
	 *
	 * @param astNode
	 *            BoogieASTNode for which Sort is computed
	 */
	public Sort getSort(IBoogieType type, final BoogieASTNode astNode) {
		if (type instanceof BoogieType) {
			type = ((BoogieType) type).getUnderlyingType();
		}
		if (mType2Sort.containsKey(type)) {
			return mType2Sort.get(type);
		}
		return constructSort(type, astNode);
	}

	private void declareType(final TypeDeclaration typeDecl) {
		final String[] typeParams = typeDecl.getTypeParams();
		if (typeParams.length != 0) {
			throw new IllegalArgumentException("Only types without parameters supported");
		}
		final String id = typeDecl.getIdentifier();

		final Map<String, Expression[]> attributes = Boogie2SmtSymbolTable.extractAttributes(typeDecl);
		if (attributes != null) {
			mType2Attributes.put(id, attributes);
			final String attributeDefinedIdentifier = Boogie2SmtSymbolTable
					.checkForAttributeDefinedIdentifier(attributes, Boogie2SmtSymbolTable.ID_BUILTIN);
			if (attributeDefinedIdentifier != null) {
				// we do not declare or define a Sort since we should use
				// a built-in Sort.
				return;
			}
		}
		if (typeDecl.getSynonym() == null) {
			mScript.declareSort(id, 0);
		} else {
			final Sort synonymSort = getSort(typeDecl.getSynonym().getBoogieType(), typeDecl);
			mScript.defineSort(id, new Sort[0], synonymSort);
		}
	}

	/**
	 * Construct the SMT sort for a Boogie type. Store the (type, sort) pair in mType2sort. Store the (sort, type) pair
	 * in msort2type.
	 *
	 * @param astNode
	 *            BoogieASTNode for which Sort is computed
	 */
	protected Sort constructSort(final IBoogieType boogieType, final BoogieASTNode astNode) {
		try {
			final Sort result = constructSort(boogieType, mType2Attributes::get);
			return result;
		} catch (final SMTLIBException e) {
			if ("Sort Array not declared".equals(e.getMessage())) {
				Boogie2SMT.reportUnsupportedSyntax(astNode, "Solver does not support arrays", mServices);
				throw e;
			}
			throw new AssertionError(e);
		}
	}

	/**
	 * Construct the SMT sort for a Boogie type. Does not use any caching and, depending on your funAttributeCache, may
	 * create many sorts.
	 */
	public Sort constructSort(final IBoogieType boogieType,
			final Function<String, Map<String, Expression[]>> funAttributeCache) {
		final Sort result;
		if (boogieType instanceof BoogiePrimitiveType) {
			if (boogieType.equals(BoogieType.TYPE_BOOL)) {
				result = SmtSortUtils.getBoolSort(mScript);
			} else if (boogieType.equals(BoogieType.TYPE_INT)) {
				result = SmtSortUtils.getIntSort(mScript);
			} else if (boogieType.equals(BoogieType.TYPE_REAL)) {
				result = SmtSortUtils.getRealSort(mScript);
			} else if (boogieType.equals(BoogieType.TYPE_ERROR)) {
				throw new IllegalArgumentException("BoogieAST contains type errors.");
			} else if (((BoogiePrimitiveType) boogieType).getTypeCode() > 0) {
				final int bitvectorSize = ((BoogiePrimitiveType) boogieType).getTypeCode();
				result = SmtSortUtils.getBitvectorSort(mScript, bitvectorSize);
			} else {
				throw new IllegalArgumentException("Unsupported PrimitiveType " + boogieType);
			}
		} else if (boogieType instanceof BoogieArrayType) {
			final BoogieArrayType arrayType = (BoogieArrayType) boogieType;
			Sort rangeSort = constructSort(arrayType.getValueType(), funAttributeCache);

			for (int i = arrayType.getIndexCount() - 1; i >= 1; i--) {
				final Sort sorti = constructSort(arrayType.getIndexType(i), funAttributeCache);
				rangeSort = SmtSortUtils.getArraySort(mScript, sorti, rangeSort);
			}
			final Sort domainSort = constructSort(arrayType.getIndexType(0), funAttributeCache);
			result = SmtSortUtils.getArraySort(mScript, domainSort, rangeSort);
		} else if (boogieType instanceof BoogieConstructedType) {
			final BoogieConstructedType constructedType = (BoogieConstructedType) boogieType;
			final String name = constructedType.getConstr().getName();
			final Map<String, Expression[]> attributes = funAttributeCache.apply(name);
			if (attributes == null) {
				result = SmtSortUtils.getNamedSort(mScript, name);
			} else {
				final String attributeDefinedIdentifier = Boogie2SmtSymbolTable
						.checkForAttributeDefinedIdentifier(attributes, Boogie2SmtSymbolTable.ID_BUILTIN);
				if (attributeDefinedIdentifier == null) {
					result = SmtSortUtils.getNamedSort(mScript, name);
				} else {
					// use SMT identifier that was defined by our "builtin"
					// attribute
					final BigInteger[] indices = Boogie2SmtSymbolTable.checkForIndices(attributes);
					result = SmtSortUtils.getBuiltinSort(mScript, attributeDefinedIdentifier, indices);
				}
			}
		} else {
			throw new IllegalArgumentException("Unsupported type " + boogieType);
		}
		cacheSort(boogieType, result);
		return result;
	}

	private void cacheSort(final IBoogieType boogieType, final Sort result) {
		mType2Sort.put(boogieType, result);
		mSort2Type.put(result, boogieType);
	}

}
