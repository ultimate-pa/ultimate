/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @deprecated The idea of this class was to introduce auxiliary variables for
 *             array indices. These auxiliary variables were part of the Jordan
 *             matrix. My hope was that these auxiliary variables simplify the
 *             construction and help us to deal with special cases where indices
 *             are array reads itself. It seems however that the algorithm that
 *             uses auxiliary variables is too complicated (one problem: it
 *             seems natural that variables are updated atomically at the end of
 *             the loop body whereas it seems natural that the index variables
 *             are assigned before the array cell is updated). Now I hope that
 *             I can avoid auxiliary variables and then this class can be
 *             delted eventually.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
@Deprecated
public class SimultaneousUpdateWithReplacements extends SimultaneousUpdate {

	private static final String ARRAY_INDEX = "arrIdx";
	private final Map<TermVariable, Term> mIdxRepAssignments;

	public SimultaneousUpdateWithReplacements(final Map<IProgramVar, Term> deterministicAssignment,
			final Map<IProgramVar, MultiDimensionalNestedStore> deterministicArrayWrites,
			final Set<IProgramVar> havocedVars, final Set<IProgramVar> readonlyVars,
			final NestedMap2<IProgramVar, ArrayIndex, Term> array2Index2value,
			final Map<TermVariable, Term> idxRepAssignments) {
		super(deterministicAssignment, deterministicArrayWrites, null, havocedVars, readonlyVars);
		mIdxRepAssignments = idxRepAssignments;
	}

	public Map<TermVariable, Term> getIdxRepAssignments() {
		return mIdxRepAssignments;
	}

	public static SimultaneousUpdateWithReplacements replaceArrayIndices(final ManagedScript mgdScript,
			final Set<TermVariable> defaultVarsOfAssignedVars, final SimultaneousUpdate su) {

		final Map<IProgramVar, Term> newDeterministicAssignments = new LinkedHashMap<>();
		final NestedMap2<IProgramVar, ArrayIndex, Term> newDeterministicArrayWrites = new NestedMap2<>();
		final Map<TermVariable, Term> idxRepAssignments = new LinkedHashMap<>();

		for (final Entry<IProgramVar, Term> entry : su.getDeterministicAssignment().entrySet()) {
			final Pair<Term, Map<TermVariable, Term>> tmp2 = replaceArrayIndices(mgdScript, defaultVarsOfAssignedVars,
					entry.getValue());
			idxRepAssignments.putAll(tmp2.getSecond());
			newDeterministicAssignments.put(entry.getKey(), tmp2.getFirst());
		}
		for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : su.getDeterministicArrayWrites().entrySet()) {
			if (entry.getValue().getIndices().size() != 1) {
				throw new AssertionError("Nested stores!");
			}
			final Pair<ArrayIndex, Map<TermVariable, Term>> tmp1 = replaceIndex(mgdScript, entry.getValue().getIndices().get(0));
			idxRepAssignments.putAll(tmp1.getSecond());
			final Pair<Term, Map<TermVariable, Term>> tmp2 = replaceArrayIndices(mgdScript, defaultVarsOfAssignedVars,
					entry.getValue().getValues().get(0));
			idxRepAssignments.putAll(tmp2.getSecond());
			newDeterministicArrayWrites.put(entry.getKey(), tmp1.getFirst(), tmp2.getFirst());
		}
		// FIXME Matthias 2023-06-04: Second argument is null. Was not willing to support this class further.
		return new SimultaneousUpdateWithReplacements(newDeterministicAssignments, null,
				su.getHavocedVars(), su.getReadonlyVars(), newDeterministicArrayWrites, idxRepAssignments);
	}

	private static Pair<ArrayIndex, Map<TermVariable, Term>> replaceIndex(final ManagedScript mgdScript,
			final ArrayIndex originalIndex) {
		final Map<TermVariable, Term> replacementMapping = new LinkedHashMap<>();
		final List<Term> indexEntries = new ArrayList<>();
		for (final Term term : originalIndex) {
			final TermVariable indexReplacement = mgdScript.constructFreshTermVariable(ARRAY_INDEX, term.getSort());
			replacementMapping.put(indexReplacement, term);
			indexEntries.add(indexReplacement);
		}
		final ArrayIndex ai = new ArrayIndex(indexEntries);
		final Pair<ArrayIndex, Map<TermVariable, Term>> res = new Pair<>(ai, replacementMapping);
		return res;
	}

	private static Pair<Term, Map<TermVariable, Term>> replaceArrayIndices(final ManagedScript mgdScript,
			final Set<TermVariable> defaultVarsOfAssignedVars, final Term term) {
		final List<MultiDimensionalSelect> tmp = MultiDimensionalSelect.extractSelectShallow(term);
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		final Map<TermVariable, Term> replacementMapping = new LinkedHashMap<>();
		for (final MultiDimensionalSelect mds : tmp) {
			if (defaultVarsOfAssignedVars.contains(mds.getArray()) || mds.getIndex().stream().anyMatch(
					x -> Arrays.asList(x.getFreeVars()).stream().anyMatch(defaultVarsOfAssignedVars::contains))) {
				// replace only if array or index is modified
				final Pair<ArrayIndex, Map<TermVariable, Term>> pair = replaceIndex(mgdScript, mds.getIndex());
				for (final Entry<TermVariable, Term> entry : pair.getSecond().entrySet()) {
					substitutionMapping.put(entry.getValue(), entry.getKey());
					replacementMapping.putAll(pair.getSecond());
				}
			}
		}
		final Term newTerm = Substitution.apply(mgdScript, substitutionMapping, term);
		final Pair<Term, Map<TermVariable, Term>> res = new Pair<>(newTerm, replacementMapping);
		return res;
	}

}
