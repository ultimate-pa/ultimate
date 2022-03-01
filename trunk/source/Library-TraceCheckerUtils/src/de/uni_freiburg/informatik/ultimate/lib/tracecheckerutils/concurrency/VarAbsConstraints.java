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
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
/*
 * Data Structure to assign constraining inVars and constraining outVars to a Letter L
 *
 */

public class VarAbsConstraints<L extends IAction> {
	// Letter mapsto a Pair of InVars(Set) and Outvars (Set)
	private final Map<L, Set<IProgramVar>> mInConstr;
	private final Map<L, Set<IProgramVar>> mOutConstr;

	public VarAbsConstraints() {
		mInConstr = new HashMap<>();
		mOutConstr = new HashMap<>();
	}

	public VarAbsConstraints(final Map<L, Set<IProgramVar>> in, final Map<L, Set<IProgramVar>> out) {
		mInConstr = in;
		mOutConstr = out;
	}

	public boolean containsLetter(final L letter) {
		return mInConstr.containsKey(letter);
	}

	public boolean containsAsInvar(final IProgramVar pv) {
		for (final Set<IProgramVar> vars : mInConstr.values()) {
			if (vars.contains(pv)) {
				return true;
			}
		}
		return false;
	}

	public boolean containsAsOutVar(final IProgramVar pv) {
		for (final Set<IProgramVar> vars : mOutConstr.values()) {
			if (vars.contains(pv)) {
				return true;
			}
		}
		return false;
	}

	public boolean containsProgramVar(final IProgramVar pv) {
		return (this.containsAsInvar(pv) || this.containsAsOutVar(pv));
	}

	public Set<L> getLetters() {
		return mInConstr.keySet();
	}

	public Set<IProgramVar> getInConstraints(final L letter) {
		return mInConstr.get(letter);
	}

	public Set<IProgramVar> getOutConstraints(final L letter) {
		return mOutConstr.get(letter);
	}

	public Map<L, Set<IProgramVar>> getCopyOfInContraintsMap() {
		return new HashMap<>(mInConstr);
	}

	public Map<L, Set<IProgramVar>> getCopyOfOutContraintsMap() {
		return new HashMap<>(mOutConstr);
	}

	public Pair<Set<L>, Set<L>> getConstrainedLetter(final IProgramVar pv) {
		final Set<L> in = Collections.emptySet();
		final Set<L> out = Collections.emptySet();
		for (final Entry<L, Set<IProgramVar>> vIn : mInConstr.entrySet()) {
			if (vIn.getValue().contains(pv)) {
				in.add(vIn.getKey());
			}
		}
		for (final Entry<L, Set<IProgramVar>> vOut : mInConstr.entrySet()) {
			if (vOut.getValue().contains(pv)) {
				out.add(vOut.getKey());
			}
		}
		return new Pair<>(in, out);
	}

	public void addNewLetter(final L letter, final Set<IProgramVar> inVars, final Set<IProgramVar> outVars) {
		mInConstr.put(letter, inVars);
		mOutConstr.put(letter, outVars);
	}

	public void addNewInLetter(final L letter, final Set<IProgramVar> inVars) {
		mInConstr.put(letter, inVars);
	}

	public void addNewOutLetter(final L letter, final Set<IProgramVar> outVars) {
		mInConstr.put(letter, outVars);
	}

	public void addInVar(final L letter, final IProgramVar inVar) {
		if (!mInConstr.containsKey(letter)) {
			this.addNewInLetter(letter, Collections.emptySet());
		}
		mInConstr.get(letter).add(inVar);

	}

	public void addInVars(final L letter, final Iterable<IProgramVar> inVars) {
		for (final IProgramVar pv : inVars) {
			this.addInVar(letter, pv);
		}
	}

	public void addOutVar(final L letter, final IProgramVar outVar) {
		if (!mOutConstr.containsKey(letter)) {
			this.addNewOutLetter(letter, Collections.emptySet());
		}
		mOutConstr.get(letter).add(outVar);
	}

	public void addOutVars(final L letter, final Iterable<IProgramVar> outVars) {
		for (final IProgramVar pv : outVars) {
			this.addOutVar(letter, pv);
		}
	}
}
