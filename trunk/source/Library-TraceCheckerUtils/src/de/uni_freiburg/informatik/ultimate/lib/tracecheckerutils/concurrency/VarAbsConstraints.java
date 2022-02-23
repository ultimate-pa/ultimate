/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
/*
 * Data Structure to assign constraining inVars and constraining outVars to a Letter L
 *
 * Caution: If a Constrain is removed the Sets for the In-Constraints and Out-Constraints aren't sound.
 */

public class VarAbsConstraints<L extends IAction> {
	// Letter mapsto a Pair of InVars(Set) and Outvars (Set)
	private final Map<L, Pair<Set<IProgramVar>, Set<IProgramVar>>> mConstr;
	private final Set<IProgramVar> mInVars;
	private final Set<IProgramVar> mOutVars;

	public VarAbsConstraints() {
		mConstr = new HashMap<>();
		mInVars = new HashSet<>();
		mOutVars = new HashSet<>();
	}

	public boolean containsLetter(final L letter) {
		return mConstr.containsKey(letter);
	}

	public boolean containsAsInvar(final IProgramVar pv) {
		return mInVars.contains(pv);
	}

	public boolean containsAsOutVar(final IProgramVar pv) {
		return mOutVars.contains(pv);
	}

	public boolean containsProgramVar(final IProgramVar pv) {
		return (this.containsAsInvar(pv) || this.containsAsOutVar(pv));
	}

	public Set<L> getLetters() {
		return mConstr.keySet();
	}

	public Pair<Set<IProgramVar>, Set<IProgramVar>> getConstraints(final L letter) {
		return mConstr.get(letter);
	}

	public Pair<Set<L>, Set<L>> getConstrainedLetter(final IProgramVar pv) {
		final Set<L> in = Collections.emptySet();
		final Set<L> out = Collections.emptySet();
		for (final Map.Entry<L, Pair<Set<IProgramVar>, Set<IProgramVar>>> pIv : mConstr.entrySet()) {
			if (pIv.getValue().getKey().contains(pv)) {
				in.add(pIv.getKey());
			}
			if (pIv.getValue().getValue().contains(pv)) {
				in.add(pIv.getKey());
			}
		}
		return new Pair<>(in, out);
	}

	public void addNewLetter(final L letter, final Set<IProgramVar> inVars, final Set<IProgramVar> outVars) {
		mConstr.put(letter, new Pair<>(inVars, outVars));
		mInVars.addAll(inVars);
		mOutVars.addAll(outVars);
	}

	public void addInVar(final L letter, final IProgramVar inVar) {
		if (mConstr.containsKey(letter)) {
			mConstr.get(letter).getKey().add(inVar);
			mInVars.add(inVar);
		}
	}

	public void addInVars(final L letter, final Iterable<IProgramVar> inVars) {
		for (final IProgramVar pv : inVars) {
			this.addInVar(letter, pv);
		}
	}

	public void addOutVar(final L letter, final IProgramVar outVar) {
		if (mConstr.containsKey(letter)) {
			mConstr.get(letter).getValue().add(outVar);
			mOutVars.add(outVar);
		}
	}

	public void addOutVars(final L letter, final Iterable<IProgramVar> outVars) {
		for (final IProgramVar pv : outVars) {
			this.addOutVar(letter, pv);
		}
	}
}
