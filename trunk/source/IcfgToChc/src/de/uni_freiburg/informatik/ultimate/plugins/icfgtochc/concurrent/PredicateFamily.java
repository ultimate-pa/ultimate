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

import java.util.ArrayDeque;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A finite indexed family of predicate symbols. The index is given by a list of {@link IHcFiniteReplacementVar}s. For
 * each combination of values of these variables, there is a unique predicate symbol.
 *
 * For instance, consider a predicate {@code P(x,y,z)}. If the first two parameters are booleans (and can thus only take
 * finitely many values), we can describe this predicate through the family consisting of the four predicates
 * {@code P_false_false(z)}, {@code P_false_true(z)}, {@code P_true_false(z)} and {@code P_true_true(z)}.
 *
 * We use this class to abstract over different modes for Horn clause generation, where certain finite parameters (e.g.
 * ICFG locations) can either be treated symbolically (using quantified variables, and possibly constraints over them)
 * or explicitly (i.e., different predicate symbols depending on the variables' values).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class PredicateFamily {
	private final HcSymbolTable mSymbolTable;
	private final PredicateInfo mBasePredicate;
	private final List<IHcFiniteReplacementVar> mIndices;

	private final List<PredicateVariant> mVariants;

	/**
	 * Creates a new indexed family of predicates.
	 *
	 * @param symbolTable
	 *            A symbol table where predicate symbols shall be declared
	 * @param basePredicate
	 *            A base predicate for the family, where all parameters are symbolic. The various predicates in the
	 *            family will be derived by removing the {@code indices} from the symbolic parameters, and making them
	 *            explicit instead.
	 * @param indices
	 *            The parameters of the base predicate that shall be made explicit.
	 */
	public PredicateFamily(final HcSymbolTable symbolTable, final PredicateInfo basePredicate,
			final List<IHcFiniteReplacementVar> indices) {
		mSymbolTable = symbolTable;
		mBasePredicate = basePredicate;
		mIndices = indices;

		mVariants = createVariants();
	}

	public PredicateInfo getBasePredicate() {
		return mBasePredicate;
	}

	public List<PredicateVariant> getVariants() {
		return mVariants;
	}

	public List<PredicateVariant> getVariants(final Map<IHcFiniteReplacementVar, Term> indexValues) {
		return mVariants.stream().filter(p -> p.matches(indexValues)).collect(Collectors.toList());
	}

	public PredicateVariant getVariant(final Map<IHcFiniteReplacementVar, Term> indexValues) {
		assert isCompleteIndexMap(indexValues);
		return DataStructureUtils.getOneAndOnly(mVariants.stream().filter(p -> p.matches(indexValues))::iterator,
				"instance");
	}

	public boolean isIndexedBy(final IHcFiniteReplacementVar variable) {
		return mIndices.contains(variable);
	}

	private List<PredicateVariant> createVariants() {
		return constructCartesianProductOfValues().stream().map(this::constructVariant).collect(Collectors.toList());
	}

	private PredicateVariant constructVariant(final ImmutableList<Term> values) {
		final var valueMap =
				IntStream.range(0, mIndices.size()).mapToObj(i -> new Pair<>(mIndices.get(i), values.get(i)))
						.collect(Collectors.toMap(Pair::getKey, Pair::getValue));
		return new PredicateVariant(mSymbolTable, this, valueMap);
	}

	private ArrayDeque<ImmutableList<Term>> constructCartesianProductOfValues() {
		final var product = new ArrayDeque<ImmutableList<Term>>();
		product.push(ImmutableList.empty());

		final var iterator = mIndices.listIterator(mIndices.size());
		while (iterator.hasPrevious()) {
			final var index = iterator.previous();
			final int size = product.size();
			for (int i = 0; i < size; ++i) {
				final var tuple = product.pollFirst();
				for (final var value : index.getAllValues()) {
					final var extendedTuple = new ImmutableList<>(value, tuple);
					product.offerLast(extendedTuple);
				}
			}
		}

		return product;
	}

	private boolean isCompleteIndexMap(final Map<IHcFiniteReplacementVar, Term> indexValues) {
		for (final var ind : mIndices) {
			final var value = indexValues.get(ind);
			if (value == null) {
				return false;
			}
			assert ind.getAllValues().contains(value) : "Wrong value for " + ind + ": " + value;
		}
		return true;
	}
}
