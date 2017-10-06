/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPStatistics;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <NODE>
 * @param <FUNCTION>
 */
public class EqDisjunctiveConstraint<
				ACTION extends IIcfgTransition<IcfgLocation>,
				NODE extends IEqNodeIdentifier<NODE>>  {

	Set<EqConstraint<ACTION, NODE>> mConstraints;

	private final EqConstraintFactory<ACTION, NODE> mFactory;

	public EqDisjunctiveConstraint(final Collection<EqConstraint<ACTION, NODE>> constraintList,
			final EqConstraintFactory<ACTION, NODE> factory) {
		assert !constraintList.stream().filter(cons -> (cons instanceof EqBottomConstraint)).findAny().isPresent()
		  : "we filter out EqBottomConstraints up front, right? (could also do it here..)";
		assert !constraintList.stream().filter(cons -> !cons.isFrozen()).findAny().isPresent()
		  : "all the constraints inside a disjunctive constraint should be frozen";
		mConstraints = new HashSet<>(constraintList);
		mFactory = factory;
	}

	public boolean isBottom() {
		return mConstraints.isEmpty();
	}

	public EqDisjunctiveConstraint<ACTION, NODE> renameVariables(final Map<Term, Term> substitutionMapping) {
		final Collection<EqConstraint<ACTION, NODE>> constraintList = new HashSet<>();
		for (final EqConstraint<ACTION, NODE> constraint : mConstraints) {
			final EqConstraint<ACTION, NODE> newConstraint = mFactory.unfreeze(constraint);
			newConstraint.renameVariables(substitutionMapping);
			newConstraint.freeze();
			constraintList.add(newConstraint);
		}
		return mFactory.getDisjunctiveConstraint(constraintList);
	}


	public EqDisjunctiveConstraint<ACTION, NODE> projectExistentially(
			final Collection<TermVariable> varsToProjectAway) {
		return mFactory.getDisjunctiveConstraint(
				mConstraints.stream()
					.map(conjConstraint -> mFactory.projectExistentially(varsToProjectAway, conjConstraint))
					.collect(Collectors.toSet()));
	}

	public Set<EqConstraint<ACTION, NODE>> getConstraints() {
		return mConstraints;
	}

	/**
	 * Return the strongest conjunctive EqConstraint that is implied by all elements of mConstraints.
	 * @return
	 */
	public EqConstraint<ACTION, NODE> flatten() {
		if (mConstraints.size() == 0) {
			return mFactory.getBottomConstraint();
		}
		if (mConstraints.size() == 1) {
			return mConstraints.iterator().next();
		}
		return mConstraints.stream().reduce((c1, c2) -> c1.join(c2)).get();
	}

	/**
	 * Convert this EqDisjunctiveConstraints to a corresponding set of EqStates. (Assumes that all the TermVariables
	 *  and nullary ApplicationTerms in this.mConstraints have a symbol table entry.)
	 * @param variablesThatTheFrameworkLikesToSee
	 * @return
	 */
	public List<EqState<ACTION>> toEqStates(final Set<IProgramVarOrConst> variablesThatTheFrameworkLikesToSee) {
//		/*
//		 *  The AbstractInterpretation framework demands that all EqStates here have the same Pvocs
//		 *  Thus we set the Pvocs of all the disjunct-states to be the union of the pvocs that each
//		 *  disjunct-state/constraint talks about.
		  // EDIT: the variables are now determined externally (by the oldstate of the post operator..)
//		 */
		return mConstraints.stream()
			.map(cons -> mFactory.getEqStateFactory().getEqState(cons, variablesThatTheFrameworkLikesToSee))
			.collect(Collectors.toList());
	}

	public boolean isEmpty() {
		return mConstraints.isEmpty();
	}

	public Term getTerm(final Script script) {
		final List<Term> disjuncts = mConstraints.stream()
				.map(cons -> cons.getTerm(script)).collect(Collectors.toList());
		return SmtUtils.or(script, disjuncts);
	}

	public boolean areEqual(final NODE node1, final NODE node2) {
		return mConstraints.stream().map(cons -> cons.areEqual(node1, node2)).reduce((a, b) -> (a || b)).get();
	}

	public boolean areUnequal(final NODE node1, final NODE node2) {
		return mConstraints.stream().map(cons -> cons.areUnequal(node1, node2)).reduce((a, b) -> (a || b)).get();
	}

//	public boolean areEqual(final FUNCTION func1, final FUNCTION func2) {
//		return mConstraints.stream().map(cons -> cons.areEqual(func1, func2)).reduce((a, b) -> (a || b)).get();
//	}
//
//	public boolean areUnequal(final FUNCTION func1, final FUNCTION func2) {
//		return mConstraints.stream().map(cons -> cons.areUnequal(func1, func2)).reduce((a, b) -> (a || b)).get();
//	}

	@Override
	public String toString() {
		if (mConstraints.isEmpty()) {
			return "EmptyDisjunction/False";
		}
		return "\\/ " + mConstraints.toString();
	}

	public String toLogString() {
		if (mConstraints.isEmpty()) {
			return "EmptyDisjunction/False";
		}
		final StringBuilder sb = new StringBuilder();
		mConstraints.forEach(c -> sb.append(c.toLogString() + "\n"));

		return "\\/ " + sb.toString();
	}


	public String getDebugInfo() {

		final Map<VPStatistics, Integer> statistics = new HashMap<>();
		for (final VPStatistics stat : VPStatistics.values()) {
			statistics.put(stat, VPStatistics.getInitialValue(stat));
		}

		final StringBuilder sb = new StringBuilder();
		for (final EqConstraint<ACTION, NODE> c : mConstraints) {
			for (final VPStatistics stat : VPStatistics.values()) {
				statistics.put(stat, VPStatistics.getAggregator(stat)
						.apply(statistics.get(stat), c.getStatistics(stat)));
			}
		}

		sb.append("EqDisjunctiveConstraint statistics:");
		sb.append(statistics);
		return sb.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mConstraints == null) ? 0 : mConstraints.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final EqDisjunctiveConstraint other = (EqDisjunctiveConstraint) obj;
		if (mConstraints == null) {
			if (other.mConstraints != null) {
				return false;
			}
		} else if (!mConstraints.equals(other.mConstraints)) {
			return false;
		}
		return true;
	}
}
