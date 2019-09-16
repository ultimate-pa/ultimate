/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders.DawgBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders.MappedDawgBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders.ProductDawgBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders.ProjectDawgBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders.ReorderDawgBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetterFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.BinaryMap;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class DawgFactory<LETTER, COLNAMES> {

	private final DawgLetterFactory<LETTER> mDawgLetterFactory;
	private final DawgStateFactory<LETTER> mDawgStateFactory;
	private final Map<Object, Set<LETTER>> mConstants = new HashMap<>();

	public DawgFactory(final EprTheory eprTheory) {
		mDawgLetterFactory = new DawgLetterFactory<>(this);
		mDawgStateFactory = new DawgStateFactory<>();
	}

	public void addConstant(final Object sortId, final LETTER ltr) {
		Set<LETTER> set = mConstants.get(sortId);
		if (set == null) {
			set = new HashSet<>();
			mConstants.put(sortId, set);
		}
		set.add(ltr);
	}

	public Set<LETTER> getAllConstants(final Object sortId) {
		if (mConstants.containsKey(sortId)) {
			return mConstants.get(sortId);
		} else {
			return Collections.emptySet();
		}
	}

	public <VALUE> DawgState<LETTER, VALUE> createConstantDawg(final SortedSet<COLNAMES> termVariables,
			final VALUE value) {
		DawgState<LETTER, VALUE> state = mDawgStateFactory.createFinalState(value);
		@SuppressWarnings("unchecked")
		final COLNAMES[] columns = (COLNAMES[]) termVariables.toArray(new Object[termVariables.size()]);
		for (int i = columns.length - 1; i >= 0; i--) {
			final COLNAMES cn = columns[i];
			final Object sort = EprHelpers.extractSortFromColname(cn);
			final DawgLetter<LETTER> letter = mDawgLetterFactory.getUniversalDawgLetter(sort);
			state = mDawgStateFactory.createIntermediateState(Collections.singletonMap(state, letter));
		}
		return state;
	}

	@SuppressWarnings("unchecked")
	public DawgState<LETTER, Boolean> createSingletonSet(final SortedSet<COLNAMES> termVariables,
			final List<LETTER> word) {

		DawgState<LETTER, Boolean> success = mDawgStateFactory.createFinalState(Boolean.TRUE);
		DawgState<LETTER, Boolean> sink = mDawgStateFactory.createFinalState(Boolean.FALSE);
		final COLNAMES[] columns = (COLNAMES[]) termVariables.toArray(new Object[termVariables.size()]);
		for (int i = columns.length - 1; i >= 0; i--) {
			final COLNAMES cn = columns[i];
			final Object sort = EprHelpers.extractSortFromColname(cn);
			final DawgLetter<LETTER> goodLetter = mDawgLetterFactory.getSingletonSetDawgLetter(word.get(i), sort);
			final DawgLetter<LETTER> badLetter = goodLetter.complement();
			final DawgLetter<LETTER> all = mDawgLetterFactory.getUniversalDawgLetter(sort);
			success = mDawgStateFactory.createIntermediateState(new BinaryMap<>(success, goodLetter, sink, badLetter));
			sink = mDawgStateFactory.createIntermediateState(Collections.singletonMap(sink, all));
		}
		return success;
	}

	@SuppressWarnings("unchecked")
	public DawgState<LETTER, Boolean> createSingletonPattern(final SortedSet<COLNAMES> termVariables,
			final List<DawgLetter<LETTER>> word) {

		DawgState<LETTER, Boolean> success = mDawgStateFactory.createFinalState(Boolean.TRUE);
		DawgState<LETTER, Boolean> sink = mDawgStateFactory.createFinalState(Boolean.FALSE);
		final COLNAMES[] columns = (COLNAMES[]) termVariables.toArray(new Object[termVariables.size()]);
		for (int i = columns.length - 1; i >= 0; i--) {
			final COLNAMES cn = columns[i];
			final Object sort = EprHelpers.extractSortFromColname(cn);
			final DawgLetter<LETTER> goodLetter = word.get(i);
			final DawgLetter<LETTER> badLetter = goodLetter.complement();
			final DawgLetter<LETTER> all = mDawgLetterFactory.getUniversalDawgLetter(sort);
			success = mDawgStateFactory.createIntermediateState(new BinaryMap<>(success, goodLetter, sink, badLetter));
			sink = mDawgStateFactory.createIntermediateState(Collections.singletonMap(sink, all));
		}
		return success;
	}

	@SuppressWarnings("unchecked")
	public DawgState<LETTER, Boolean> createPatternMatchSet(final SortedSet<COLNAMES> termVariables,
			final List<LETTER> word) {

		DawgState<LETTER, Boolean> success = mDawgStateFactory.createFinalState(Boolean.TRUE);
		DawgState<LETTER, Boolean> sink = mDawgStateFactory.createFinalState(Boolean.FALSE);
		final COLNAMES[] columns = (COLNAMES[]) termVariables.toArray(new Object[termVariables.size()]);
		for (int i = columns.length - 1; i >= 0; i--) {
			final COLNAMES cn = columns[i];
			final Object sort = EprHelpers.extractSortFromColname(cn);
			final DawgLetter<LETTER> all = mDawgLetterFactory.getUniversalDawgLetter(sort);
			if (word.get(i) == null) {
				success = mDawgStateFactory.createIntermediateState(Collections.singletonMap(success, all));
			} else {
				final DawgLetter<LETTER> goodLetter = mDawgLetterFactory.getSingletonSetDawgLetter(word.get(i), sort);
				final DawgLetter<LETTER> badLetter = goodLetter.complement();
				success = mDawgStateFactory
						.createIntermediateState(new BinaryMap<>(success, goodLetter, sink, badLetter));
			}
			sink = mDawgStateFactory.createIntermediateState(Collections.singletonMap(sink, all));
		}
		return success;
	}

	public DawgState<LETTER, Boolean> createFromSelectMap(final SortedSet<COLNAMES> termVariables,
			final Map<COLNAMES, LETTER> selectMap) {

		DawgState<LETTER, Boolean> success = mDawgStateFactory.createFinalState(Boolean.TRUE);
		DawgState<LETTER, Boolean> sink = mDawgStateFactory.createFinalState(Boolean.FALSE);
		@SuppressWarnings("unchecked")
		final COLNAMES[] columns = (COLNAMES[]) termVariables.toArray(new Object[termVariables.size()]);
		for (int i = columns.length - 1; i >= 0; i--) {
			final COLNAMES cn = columns[i];
			final Object sort = EprHelpers.extractSortFromColname(cn);
			final DawgLetter<LETTER> all = mDawgLetterFactory.getUniversalDawgLetter(sort);
			if (selectMap.containsKey(columns[i])) {
				final DawgLetter<LETTER> goodLetter =
						mDawgLetterFactory.getSingletonSetDawgLetter(selectMap.get(columns[i]), sort);
				final DawgLetter<LETTER> badLetter = goodLetter.complement();
				success = mDawgStateFactory
						.createIntermediateState(new BinaryMap<>(success, goodLetter, sink, badLetter));
			} else {
				success = mDawgStateFactory.createIntermediateState(Collections.singletonMap(success, all));
			}
			sink = mDawgStateFactory.createIntermediateState(Collections.singletonMap(sink, all));
		}
		return success;
	}

	public <V1, V2> DawgState<LETTER, V2> createMapped(final DawgState<LETTER, V1> first,
			final java.util.function.Function<V1, V2> map) {
		final MappedDawgBuilder<LETTER, COLNAMES, V1, V2> builder = new MappedDawgBuilder<>(this, map);
		return builder.map(first);
	}

	public <V1, V2, V3> DawgState<LETTER, V3> createProduct(final DawgState<LETTER, V1> first,
			final DawgState<LETTER, V2> second, final java.util.function.BiFunction<V1, V2, V3> combinator) {
		final ProductDawgBuilder<LETTER, COLNAMES, V1, V2, V3> builder = new ProductDawgBuilder<>(this, combinator);
		return builder.product(first, second);
	}

	public DawgState<LETTER, Boolean> createDifference(final DawgState<LETTER, Boolean> first,
			final DawgState<LETTER, Boolean> second) {
		return createProduct(first, second, (in1, in2) -> in1 && !in2);
	}

	public DawgState<LETTER, Boolean> createUnion(final DawgState<LETTER, Boolean> first,
			final DawgState<LETTER, Boolean> second) {
		return createProduct(first, second, (in1, in2) -> in1 || in2);
	}

	public DawgState<LETTER, Boolean> createIntersection(final DawgState<LETTER, Boolean> first,
			final DawgState<LETTER, Boolean> second) {
		return createProduct(first, second, (in1, in2) -> in1 && in2);
	}

	private <VALUE> DawgState<LETTER, VALUE> projectWithMapInternal(final DawgState<LETTER, VALUE> dawg,
			final LETTER[] selectMap, final int level) {
		if (dawg.isFinal()) {
			return dawg;
		} else if (selectMap[level] != null) {
			final LETTER ltr = selectMap[level];
			for (final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> trans : dawg.getTransitions()
					.entrySet()) {
				if (trans.getValue().matches(ltr)) {
					return projectWithMapInternal(trans.getKey(), selectMap, level + 1);
				}
			}
			throw new AssertionError();
		} else {
			final Map<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> newTransitions = new HashMap<>();
			for (final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> trans : dawg.getTransitions()
					.entrySet()) {
				final DawgState<LETTER, VALUE> newState = projectWithMapInternal(trans.getKey(), selectMap, level + 1);
				DawgBuilder.addLetterToMap(newTransitions, newState, trans.getValue());
			}
			return mDawgStateFactory.createIntermediateState(newTransitions);
		}
	}

	public <VALUE> DawgState<LETTER, VALUE> projectWithMap(final DawgState<LETTER, VALUE> dawg, LETTER[] selectMap) {
		return projectWithMapInternal(dawg, selectMap, 0);
	}

	public static <LETTER, VALUE> boolean isConstantValue(final DawgState<LETTER, VALUE> state, final VALUE value) {
		if (state.isFinal()) {
			return state.getFinalValue() == value;
		} else {
			return state.getTransitions().size() == 1 &&
					isConstantValue(state.getTransitions().keySet().iterator().next(), value);
		}
	}

	public static <LETTER> boolean isUniversal(final DawgState<LETTER, Boolean> state) {
		return isConstantValue(state, Boolean.TRUE);
	}

	public static <LETTER> boolean isEmpty(final DawgState<LETTER, Boolean> state) {
		return isConstantValue(state, Boolean.FALSE);
	}

	public static <LETTER> Iterable<List<LETTER>> getSet(final DawgState<LETTER, Boolean> state) {
		if (state.isFinal()) {
			return state.getFinalValue() ? Collections.singleton(Collections.emptyList()) : Collections.emptySet();
		}
		return new Iterable<List<LETTER>>() {
			@Override
			public Iterator<List<LETTER>> iterator() {
				return new Iterator<List<LETTER>>() {
					Iterator<DawgState<LETTER, Boolean>> transIterator = state.getTransitions().keySet().iterator();
					DawgState<LETTER, Boolean> currentSubState = transIterator.next();
					Iterator<LETTER> letterIterator = state.getTransitions().get(currentSubState).getLetters().iterator();
					LETTER currentLetter;
					Iterator<List<LETTER>> subIterator = null;

					@Override
					public boolean hasNext() {
						while (subIterator == null || !subIterator.hasNext()) {
							while (!letterIterator.hasNext()) {
								if (!transIterator.hasNext()) {
									return false;
								}
								currentSubState = transIterator.next();
								letterIterator = state.getTransitions().get(currentSubState).getLetters().iterator();
							}
							currentLetter = letterIterator.next();
							subIterator = getSet(currentSubState).iterator();
						}
						return true;
					}

					@Override
					public List<LETTER> next() {
						final List<LETTER> currentSuffix = subIterator.next();
						final List<LETTER> result = new ArrayList<>(currentSuffix.size() + 1);
						result.add(currentLetter);
						result.addAll(currentSuffix);
						return result;
					}
				};
			}
		};
	}

	public DawgLetterFactory<LETTER> getDawgLetterFactory() {
		return mDawgLetterFactory;
	}

	public DawgStateFactory<LETTER> getDawgStateFactory() {
		return mDawgStateFactory;
	}

	public DawgState<LETTER, Boolean>
			computeSymmetricTransitiveClosure(final DawgState<LETTER, Boolean> binRelation) {
		final Object sort = binRelation.getTransitions().values().iterator().next().getSortId();
		final Set<DawgLetter<LETTER>> partitions = new HashSet<>();
		for (final Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> trans1 : binRelation.getTransitions().entrySet()) {
			if (!isEmpty(trans1.getKey())) {
				partitions.add(trans1.getValue());
			}
		}
		for (final Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> trans1 : binRelation.getTransitions().entrySet()) {
			for (final Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> trans2 : trans1.getKey().getTransitions().entrySet()) {
				if (trans2.getKey().getFinalValue() == Boolean.TRUE) {
					// compute elements that are not yet in first partition, but must be merged.
					final DawgLetter<LETTER> newElems = trans2.getValue().difference(trans1.getValue());
					if (!newElems.isEmpty()) {
						final DawgLetter<LETTER> union = trans1.getValue().union(trans2.getValue());
						DawgLetter<LETTER> newPart = trans2.getValue();
						final Iterator<DawgLetter<LETTER>> it = partitions.iterator();
						while (it.hasNext()) {
							final DawgLetter<LETTER> otherPart = it.next();
							if (!otherPart.isDisjoint(union)) {
								newPart = newPart.union(otherPart);
								it.remove();
							}
						}
						partitions.add(newPart);
					}
				}
			}
		}
		final Map<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> firstTrans = new HashMap<>();
		final DawgLetter<LETTER> all = mDawgLetterFactory.getUniversalDawgLetter(sort);
		final DawgState<LETTER, Boolean> sink = mDawgStateFactory.createFinalState(Boolean.FALSE);
		final DawgState<LETTER, Boolean> good = mDawgStateFactory.createFinalState(Boolean.TRUE);
		DawgLetter<LETTER> remainder = all;
		for (final DawgLetter<LETTER> letter : partitions) {
			assert !letter.isEmpty();
			// if (!letter.isSingleton()) {
			// continue;
			// }
			remainder = remainder.difference(letter);
			final DawgState<LETTER, Boolean> intermediate =
					mDawgStateFactory.createIntermediateState(new BinaryMap<>(good, letter, sink, letter.complement()));
			firstTrans.put(intermediate, letter);
		}
		firstTrans.put(mDawgStateFactory.createIntermediateState(Collections.singletonMap(sink, all)), remainder);
		return mDawgStateFactory.createIntermediateState(firstTrans);
	}

	public static <LETTER> boolean isSingleton(final DawgState<LETTER, Boolean> dawg) {
		if (dawg.isFinal()) {
			return dawg.getFinalValue();
		}
		boolean foundSingleton = false;
		for (final Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> entry : dawg.getTransitions().entrySet()) {
			if (isEmpty(entry.getKey())) {
				continue;
			}
			if (foundSingleton || !entry.getValue().isSingleton() || !isSingleton(entry.getKey())) {
				return false;
			}
			foundSingleton = true;
		}
		return foundSingleton;
	}

	/**
	 * Used for translating from the signature of a DecideStackLiteral to the signature of an EprClause with respect to
	 * a clause literals signature. A DecideStackLiteral has one variable for each argument of the underlying predicate.
	 *
	 * example: - some DSL says something like P(x_0 x_1 x_2 x_3) - the overall clause signature may be (u v w x y z) -
	 * the clause literals arguments may be (v a w v) (i.e. there may be constants, repetitions, and different
	 * orderings)
	 *
	 * the input dawg has the signature of the DSL
	 *
	 * then we want to change the columns of the input dawg such that they match the clause's signature this entails -
	 * renamings -- x_0 -> v, x_2 -> w - if there are repetitions or constants, we have to select accordingly, in the
	 * example we only select points where x_0 = x_3 and x_1 = a --> from this we would get a dawg that describes the
	 * points wrt the clause literal - we have to blow up the signature for the whole clause, i.e., for every missing
	 * column to the target signature we insert a "X Sigma", i.e., we compute the cross product with the whole set of
	 * constants
	 *
	 *
	 * In short, and in the applications of the EprTheory, this translates a Dawg with the signature of an EprPredicate
	 * to a Dawg with the signature of a clause (according to the given translation mapping that is stored in each
	 * ClauseEprQuantifiedPredicate)
	 *
	 * @param dawg
	 *            the dawg that is to be transformed
	 * @param translation
	 *            a mapping from the variables in the input Dawgs signature to other TermVariables and/or constants
	 * @param targetSignature
	 *            the target signature we want to blow up for in the end
	 * @return
	 */
	public <VALUE> DawgState<LETTER, VALUE> remap(DawgState<LETTER, VALUE> dawg, int[] columnMap, 
			SortedSet<COLNAMES> clauseVariables) {
		int numVars = 0;
		for (int i = 0; i < columnMap.length; i++) {
			if (columnMap[i] >= 0) {
				numVars++;
			}
		}
		final List<DawgLetter<LETTER>> clauseWord = new ArrayList<>(clauseVariables.size());
		for (final COLNAMES tv : clauseVariables) {
			final Object sort = EprHelpers.extractSortFromColname(tv);
			clauseWord.add(mDawgLetterFactory.getUniversalDawgLetter(sort));
		}
		int[] columnIndexCompressed = new int[numVars];
		int compressedIdx = 0;
		for (int i = 0; i < columnMap.length; i++) {
			if (columnMap[i] >= 0) {
				columnIndexCompressed[compressedIdx++] = columnMap[i];
				clauseWord.set(columnMap[i], null);
			}
		}
		dawg = new ReorderDawgBuilder<LETTER, VALUE, COLNAMES>(this).reorder(dawg, clauseWord, columnIndexCompressed);
		return dawg;
	}

	/**
	 * From the input dawg and translation computes a dawg
	 *  - whose points are rearranged according to the new signature
	 *  - constants in the argList are filled in the corresponding places at every point
	 *  - we exploit that the order of arglist matches the sorting order of the newSignature
	 *    (that is fix for the given eprPredicate)
	 *  EDIT:
	 *   Pragmatically spoken this translated a dawg in the signature of an epr clause into a dawg in the signature of
	 *   a decide stack literal. For this it uses the information from one clause literal whose predicate matches the
	 *   decide stack literal's predicate.
	 * @param other
	 * @param binaryRelation a map translating the colnames of the old dawg ("other") to the colnames of the new dawg
	 *                    may not have a preimage for every new colname in the new signature because there constants
	 *                    from argList are filled in
	 *                     (could be computed from arglist, right?..)
	 * @param argList
	 * @param newSignature
	 * @return
	 */
	public DawgState<LETTER, Boolean> translateClauseSigToPredSig(
			DawgState<LETTER, Boolean> dawg,
			final int[] clausePos2predPos,
			final LETTER[] groundArguments, SortedSet<COLNAMES> predVariables) {
		final List<DawgLetter<LETTER>> predWord = new ArrayList<>(groundArguments.length);
		int index = 0;
		for (COLNAMES tv : predVariables) {
			final Object sort = EprHelpers.extractSortFromColname(tv);
			if (groundArguments[index] == null) {
				predWord.add(null);
			} else {
				predWord.add(mDawgLetterFactory.getUniversalDawgLetter(sort));
			}
			index++;
		}
		int numOccuringVars = 0;
		for (int i = 0; i < clausePos2predPos.length; i++) {
			if (clausePos2predPos[i] >= 0) {
				numOccuringVars++;
			}
		}
		final int[] columnIndexMap = new int[numOccuringVars];
		final BitSet clauseVarInUse = new BitSet();
		int projectedIndex = 0;
		for (int i = 0; i < clausePos2predPos.length; i++) {
			if (clausePos2predPos[i] >= 0) {
				columnIndexMap[projectedIndex] = clausePos2predPos[i];
				assert predWord.get(columnIndexMap[projectedIndex]) == null;
				clauseVarInUse.set(i);
				projectedIndex++;
			}
		}
		dawg = new ProjectDawgBuilder<>(this, clausePos2predPos.length, clauseVarInUse).project(dawg);
		dawg = new ReorderDawgBuilder<LETTER, Boolean, COLNAMES>(this).reorder(dawg, predWord, columnIndexMap);
		dawg = createIntersection(dawg, createPatternMatchSet(predVariables, Arrays.asList(groundArguments)));
		return dawg;
	}

	public static <LETTER> List<DawgLetter<LETTER>> getOneWord(DawgState<LETTER, Boolean> dawg) {
		assert !isEmpty(dawg);
		List<DawgLetter<LETTER>> word = new ArrayList<>();
		while (!dawg.isFinal()) {
			for (Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> entry : dawg.getTransitions().entrySet()) {
				if (!isEmpty(entry.getKey())) {
					word.add(entry.getValue());
					dawg = entry.getKey();
					break;
				}
			}
			assert !isEmpty(dawg);
		}
		return word;
	}
}
