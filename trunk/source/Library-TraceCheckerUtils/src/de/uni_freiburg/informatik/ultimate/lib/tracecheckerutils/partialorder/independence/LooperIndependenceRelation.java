/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ISymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ILooperCheck;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;

public class LooperIndependenceRelation<L extends IAction, S> implements IIndependenceRelation<S, L> {
	private final Set<IPredicate> mPredicates;
	private final ILooperCheck<L> mLooperCheck;
	private final ILattice<Set<IPredicate>> mHierarchy = new UpsideDownLattice<>(new PowersetLattice<>());

	public LooperIndependenceRelation(final Set<IPredicate> predicates, final ILooperCheck<L> looperCheck) {
		mPredicates = predicates;
		mLooperCheck = looperCheck;
	}

	@Override
	public boolean isSymmetric() {
		return true;
	}

	@Override
	public boolean isConditional() {
		return false;
	}

	@Override
	public Dependence isIndependent(final S state, final L a, final L b) {
		final LBool aLooper = mLooperCheck.isUniversalLooper(a, mPredicates);
		if (aLooper == LBool.UNSAT) {
			return Dependence.INDEPENDENT;
		}

		final LBool bLooper = mLooperCheck.isUniversalLooper(b, mPredicates);
		if (bLooper == LBool.UNSAT) {
			return Dependence.INDEPENDENT;
		}

		if (aLooper == LBool.UNKNOWN || bLooper == LBool.UNKNOWN) {
			return Dependence.UNKNOWN;
		}
		return Dependence.DEPENDENT;
	}

	@Override
	public ISymbolicIndependenceRelation<L, S> getSymbolicRelation() {
		// Since the relation is unconditional, there is no corresponding symbolic relation.
		return null;
	}

	public ILattice<Set<IPredicate>> getHierarchy() {
		return mHierarchy;
	}

	public Set<IPredicate> getInitial() {
		return mHierarchy.getTop();
	}

	public static <L extends IIcfgTransition<?>> Set<IPredicate> refine(final Set<IPredicate> current,
			final IRefinementEngineResult<L, ?> refinement) {
		final Set<IPredicate> newPredicates = refinement.getUsedTracePredicates().stream()
				.flatMap(tp -> tp.getPredicates().stream()).collect(Collectors.toSet());
		return DataStructureUtils.union(current, newPredicates);
	}
}
