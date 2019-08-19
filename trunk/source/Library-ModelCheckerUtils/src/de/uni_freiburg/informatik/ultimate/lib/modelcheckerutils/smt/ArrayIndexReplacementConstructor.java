/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

/**
 *
 * TODO: Maybe do replacement by nice alternatives here
 * @author heizmann@informatik.uni-freiburg.de
 *
 *
 */
public class ArrayIndexReplacementConstructor {

	private final TermVariable mForbiddenTv;
	private final ConstructionCache<Term, Term> mEntryConstrCache;
	private final ConstructionCache<ArrayIndex, ArrayIndex> mIndexConstrCache;
	private final Map<TermVariable, Term> mAuxVar2Definition = new LinkedHashMap<>();
	private boolean mConstructionDone;

	public ArrayIndexReplacementConstructor(final ManagedScript mgdScript, final String auxVarPrefix,
			final TermVariable forbiddenTv) {
		mForbiddenTv = forbiddenTv;

		final IValueConstruction<Term, Term> entryValueConstruction = new IValueConstruction<Term, Term>() {

			@Override
			public Term constructValue(final Term indexEntry) {
				final TermVariable entryReplacement = mgdScript.constructFreshTermVariable(auxVarPrefix,
						indexEntry.getSort());
				mAuxVar2Definition.put(entryReplacement, indexEntry);
				return entryReplacement;
			}

		};
		mEntryConstrCache = new ConstructionCache<>(entryValueConstruction);

		final IValueConstruction<ArrayIndex, ArrayIndex> indexValueConstruction = new IValueConstruction<ArrayIndex, ArrayIndex>() {

			@Override
			public ArrayIndex constructValue(final ArrayIndex index) {
				final List<Term> resultIndexEntries = new ArrayList<>();
				for (int i = 0; i < index.size(); i++) {
					final Term entry = index.get(i);
					Term newEntry;
					if (entryContainsForbiddenTv(entry)) {
						newEntry = mEntryConstrCache.getOrConstruct(entry);
					} else {
						newEntry = entry;
					}
					resultIndexEntries.add(newEntry);
				}
				return new ArrayIndex(resultIndexEntries);
			}

		};
		mIndexConstrCache = new ConstructionCache<>(indexValueConstruction);
	}

	private boolean entryContainsForbiddenTv(final Term entry) {
		return Arrays.asList(entry.getFreeVars()).contains(mForbiddenTv);
	}

	private boolean indexContainsForbiddenTv(final ArrayIndex index) {
		return index.stream().anyMatch(x -> entryContainsForbiddenTv(x));
	}

	public ArrayIndex constructIndexReplacementIfNeeded(final ArrayIndex index) {
		if (mConstructionDone) {
			throw new IllegalStateException("Definitions already constructed or auxVars already returned");
		}
		final ArrayIndex result;
		if (indexContainsForbiddenTv(index)) {
			result = mIndexConstrCache.getOrConstruct(index);
		} else {
			result = index;
		}
		return result;
	}

	public Term constructTermReplacementIfNeeded(final Term term) {
		if (mConstructionDone) {
			throw new IllegalStateException("Definitions already constructed or auxVars already returned");
		}
		final Term result;
		if (entryContainsForbiddenTv(term)) {
			result = mEntryConstrCache.getOrConstruct(term);
		} else {
			result = term;
		}
		return result;
	}

	public Set<TermVariable> getConstructedAuxVars() {
		mConstructionDone = true;
		return mAuxVar2Definition.keySet();
	}

	public Term constructDefinitions(final Script script, final int quantifier) {
		mConstructionDone = true;
		final List<Term> dualJuncts = mAuxVar2Definition.entrySet().stream()
				.map(x -> QuantifierUtils.applyDerOperator(script, quantifier, x.getKey(), x.getValue()))
				.collect(Collectors.toList());
		final Term dualJunction = QuantifierUtils.applyDualFiniteConnective(script, quantifier, dualJuncts);
		return dualJunction;
	}




}
