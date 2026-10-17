/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem.StepVars;

/**
 * Unrolling of a {@link PcTransitionSystem} with constants, for solver queries. Auxiliary variables are separate
 * constants per transition and step, so different steps do not share their values.
 * <p>
 * A constant is declared the first time it is asked for. Constants declared inside a {@code push} are forgotten by the
 * solver on {@code pop} but stay in the cache, so everything a query needs has to be asked for before its push.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class IndexedConstantVars implements StepVars {
	private final Script mScript;
	private final Map<String, Term> mCache;
	private final String mPrefix;
	private final Sort mPcSort;

	/**
	 * @param cache
	 *            the declared constants, shared by every query on {@code script}
	 * @param prefix
	 *            put in front of the names of the pc, selector and auxiliary constants
	 */
	public IndexedConstantVars(final Script script, final Map<String, Term> cache, final String prefix) {
		mScript = script;
		mCache = cache;
		mPrefix = prefix;
		mPcSort = PcTransitionSystem.pcValue(script, 0).getSort();
	}

	@Override
	public Term var(final IProgramVar pv, final int idx) {
		return PredicateUtils.getIndexedConstant(pv, idx, mCache, mScript);
	}

	@Override
	public Term pc(final int idx) {
		return PredicateUtils.getIndexedConstant(mPrefix + "pc", mPcSort, idx, mCache, mScript);
	}

	@Override
	public Term aux(final int transitionId, final TermVariable auxVar, final int idx) {
		return PredicateUtils.getIndexedConstant(mPrefix + "aux_" + transitionId + "_" + auxVar.getName(),
				auxVar.getSort(), idx, mCache, mScript);
	}

	@Override
	public Term sel(final int idx) {
		return PredicateUtils.getIndexedConstant(mPrefix + "sel", mPcSort, idx, mCache, mScript);
	}
}
