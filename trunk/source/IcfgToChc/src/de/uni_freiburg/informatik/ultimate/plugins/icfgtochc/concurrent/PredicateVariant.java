/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A member of a {@link PredicateFamily}, where the family's indices have been fixed to concrete values.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class PredicateVariant extends PredicateInfo {
	private final PredicateFamily mFamily;
	private final Map<IHcFiniteReplacementVar, Term> mIndexValues;

	PredicateVariant(final HcSymbolTable symbolTable, final PredicateFamily family,
			final Map<IHcFiniteReplacementVar, Term> indexValues) {
		this(symbolTable, family, indexValues,
				projectParameters(family.getBasePredicate().mParameters, indexValues.keySet()));
	}

	private PredicateVariant(final HcSymbolTable symbolTable, final PredicateFamily family,
			final Map<IHcFiniteReplacementVar, Term> indexValues, final List<IHcReplacementVar> parameters) {
		super(instantiatePredicate(symbolTable, family.getBasePredicate(), indexValues, parameters), parameters);
		mFamily = family;
		mIndexValues = indexValues;
	}

	/**
	 * Determines if this instance has the given values for its indices. Values for parameters which are not indices are
	 * ignored.
	 *
	 * @param indexMap
	 *            Maps certain variables to values. May include mappings for variables that are not indices (ignored),
	 *            and may omit mappings for some of the indices (can have any value).
	 * @return {@code true} if for all indices of this predicate that are present in the map, the instance's value
	 *         equals the value in the map; {@code false} otherwise.
	 */
	public boolean matches(final Map<IHcFiniteReplacementVar, Term> indexMap) {
		for (final var entry : indexMap.entrySet()) {
			final var variable = entry.getKey();
			if (mFamily.isIndexedBy(variable) && !Objects.equals(entry.getValue(), mIndexValues.get(variable))) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Determines if the given variable is an index of this predicate variant (i.e., the predicate fixes a value of the
	 * variable).
	 */
	public boolean hasIndex(final IHcFiniteReplacementVar variable) {
		return mFamily.isIndexedBy(variable);
	}

	/**
	 * Retrieves the fixed value of the given variable associated with this predicate variant. The variable must be an
	 * index of the predicate variant (see {@link #hasIndex(IHcFiniteReplacementVar)}).
	 */
	public Term getIndexValue(final IHcFiniteReplacementVar variable) {
		assert hasIndex(variable) : variable + " is not an index of this predicate variant";
		return mIndexValues.get(variable);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + Objects.hash(mFamily, mIndexValues);
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!super.equals(obj)) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final PredicateVariant other = (PredicateVariant) obj;
		return Objects.equals(mFamily, other.mFamily) && Objects.equals(mIndexValues, other.mIndexValues);
	}

	private static HcPredicateSymbol instantiatePredicate(final HcSymbolTable symbolTable,
			final PredicateInfo predicate, final Map<IHcFiniteReplacementVar, Term> indexValues,
			final List<IHcReplacementVar> parameters) {
		final var name = constructInstanceName(predicate.getPredicate().getName(), indexValues);
		final var paramSorts = parameters.stream().map(IHcReplacementVar::getSort).collect(Collectors.toList());
		return symbolTable.getOrConstructHornClausePredicateSymbol(name, paramSorts);
	}

	private static String constructInstanceName(final String basename,
			final Map<IHcFiniteReplacementVar, Term> indexValues) {
		final var name = new StringBuilder(basename);

		for (final var entry : indexValues.entrySet()) {
			name.append("_");
			name.append(entry.getKey());
			name.append("=");
			name.append(entry.getValue());
		}

		return name.toString();
	}

	private static List<IHcReplacementVar> projectParameters(final List<IHcReplacementVar> parameters,
			final Set<IHcFiniteReplacementVar> indices) {
		return parameters.stream().filter(p -> !indices.contains(p)).collect(Collectors.toList());
	}
}
