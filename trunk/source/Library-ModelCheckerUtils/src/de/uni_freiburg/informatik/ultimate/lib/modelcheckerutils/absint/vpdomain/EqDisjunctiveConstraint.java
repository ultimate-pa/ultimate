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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <NODE>
 * @param <FUNCTION>
 */
public class EqDisjunctiveConstraint<NODE extends IEqNodeIdentifier<NODE>>  {

	private final Set<EqConstraint<NODE>> mConstraints;

	private final EqConstraintFactory<NODE> mFactory;

	private final AbstractNodeAndFunctionFactory<NODE, Term> mNodeAndFunctionFactory;

	public EqDisjunctiveConstraint(final Collection<EqConstraint<NODE>> constraintList,
			final EqConstraintFactory<NODE> factory) {
		assert !constraintList.stream().filter(cons -> (cons instanceof EqBottomConstraint)).findAny().isPresent()
		  : "we filter out EqBottomConstraints up front, right? (could also do it here..)";
//		assert !constraintList.stream().filter(cons -> !cons.isFrozen()).findAny().isPresent()
//		  : "all the constraints inside a disjunctive constraint should be frozen";
		mConstraints = new HashSet<>(constraintList);
		mFactory = factory;
		mNodeAndFunctionFactory = factory.getEqNodeAndFunctionFactory();
	}

	public boolean isBottom() {
		return mConstraints.isEmpty();
	}

	public EqDisjunctiveConstraint<NODE> projectExistentially(final Collection<Term> termsToProjectAway) {
		final Collection<EqConstraint<NODE>> newConstraints = new ArrayList<>();
		for (final EqConstraint<NODE> c : mConstraints) {
			newConstraints.add(mFactory.projectExistentially(termsToProjectAway, c, false));
		}
		return mFactory.getDisjunctiveConstraint(newConstraints);
	}

	public Set<EqConstraint<NODE>> getConstraints() {
		return Collections.unmodifiableSet(mConstraints);
	}

	/**
	 * Computes the join of all the (purely conjunctive) EqConstraints that form the disjuncts of this
	 * EqDisjunctiveCostraint.
	 *
	 * @return the join of all constraints in getConstraints()
	 */
	public EqConstraint<NODE> flatten() {
		if (mConstraints.size() == 0) {
			return mFactory.getBottomConstraint();
		}
		if (mConstraints.size() == 1) {
			return mConstraints.iterator().next();
		}
		return mConstraints.stream().reduce((c1, c2) -> c1.join(c2)).get();
		// this caused a loop as disjoin uses flatten..
//		return mConstraints.stream().reduce((c1, c2) -> mFactory.disjoin(c1, c2)).get();
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
		return mConstraints.stream().map(cons -> cons.areEqual(node1, node2,
				mFactory.getWeqSettings().isAddNodesBeforeAnsweringQuery())).reduce((a, b) -> (a || b)).get();
	}

	public boolean areEqual(final Term node1, final Term node2) {
		final NODE n1 = mNodeAndFunctionFactory.getExistingNode(node1);
		if (n1 == null) {
			return false;
		}
		final NODE n2 = mNodeAndFunctionFactory.getExistingNode(node2);
		if (n2 == null) {
			return false;
		}
		return areEqual(n1, n2);
	}

	public boolean areUnequal(final NODE node1, final NODE node2) {
		return mConstraints.stream().map(cons -> cons.areUnequal(node1, node2,
				mFactory.getWeqSettings().isAddNodesBeforeAnsweringQuery())).reduce((a, b) -> (a || b)).get();
	}

	public boolean areUnequal(final Term node1, final Term node2) {
		final NODE n1 = mNodeAndFunctionFactory.getExistingNode(node1);
		if (n1 == null) {
			return false;
		}
		final NODE n2 = mNodeAndFunctionFactory.getExistingNode(node2);
		if (n2 == null) {
			return false;
		}
		return areUnequal(n1, n2);
	}

	private EqDisjunctiveConstraint<NODE> reportEquality(final NODE node1, final NODE node2) {
		final Collection<EqConstraint<NODE>> constraintList = new ArrayList<>();
		for (final EqConstraint<NODE> constraint : mConstraints) {
			EqConstraint<NODE> unfrozen = mFactory.unfreeze(constraint);
			unfrozen.reportEqualityInPlace(node1, node2);

			if (mFactory.getWeqCcManager().getSettings().closeAllEqConstraints()) {
				unfrozen = mFactory.closeIfNecessary(unfrozen);
			}
			unfrozen.freezeIfNecessary();

			constraintList.add(unfrozen);
		}
		return mFactory.getDisjunctiveConstraint(constraintList);
	}

	public EqDisjunctiveConstraint<NODE> reportEquality(final Term node1, final Term node2) {
		final NODE n1 = mNodeAndFunctionFactory.getOrConstructNode(node1);
		final NODE n2 = mNodeAndFunctionFactory.getOrConstructNode(node2);
		return reportEquality(n1, n2);
	}

	private EqDisjunctiveConstraint<NODE> reportDisequality(final NODE node1, final NODE node2) {
		final Collection<EqConstraint<NODE>> constraintList = new ArrayList<>();
		for (final EqConstraint<NODE> constraint : mConstraints) {
			EqConstraint<NODE> unfrozen = mFactory.unfreeze(constraint);
			unfrozen.reportDisequalityInPlace(node1, node2);

			if (mFactory.getWeqCcManager().getSettings().closeAllEqConstraints()) {
				unfrozen = mFactory.closeIfNecessary(unfrozen);
			}
			unfrozen.freezeIfNecessary();

			constraintList.add(unfrozen);
		}
		return mFactory.getDisjunctiveConstraint(constraintList);
	}

	public EqDisjunctiveConstraint<NODE> reportDisequality(final Term node1, final Term node2) {
		final NODE n1 = mNodeAndFunctionFactory.getOrConstructNode(node1);
		final NODE n2 = mNodeAndFunctionFactory.getOrConstructNode(node2);
		return reportDisequality(n1, n2);
	}

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
		for (final EqConstraint<NODE> c : mConstraints) {
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

	public Integer getStatistics(final VPStatistics stat) {
		switch (stat) {
		case NO_DISJUNCTIONS:
		case MAX_NO_DISJUNCTIONS:
			return mConstraints.size();
		default:
			Integer val = VPStatistics.getInitialValue(stat);
			for (final EqConstraint<NODE> c : mConstraints) {
				val = VPStatistics.getAggregator(stat).apply(val, c.getStatistics(stat));
			}
			return val;
		}
	}

	public EqDisjunctiveConstraint<NODE> closeDisjunctsIfNecessary() {
		if (mConstraints.stream().allMatch(c -> c.isClosed())) {
			return this;
		}
		final Collection<EqConstraint<NODE>> constraintList = new HashSet<>();
		for (final EqConstraint<NODE> disjunct : mConstraints) {
			constraintList.add(mFactory.closeIfNecessary(disjunct));
		}
		return mFactory.getDisjunctiveConstraint(constraintList);
	}


	public void freezeDisjunctsIfNecessary() {
		for (final EqConstraint<NODE> disjunct : mConstraints) {
			disjunct.freezeIfNecessary();
		}
	}

	public Set<NODE> getAllLiteralNodes() {
		final Set<NODE> result = new HashSet<>();
		for (final EqConstraint<NODE> c : mConstraints) {
			result.addAll(c.getAllLiteralNodes());
		}
		return result;
	}

	public EqConstraintFactory<NODE> getFactory() {
		return mFactory;
	}

	public Set<Term> getSetConstraintForExpression(final Term exp) {
		final NODE node = mNodeAndFunctionFactory.getOrConstructNode(exp);

		final EqConstraint<NODE> flat = this.flatten();

		final Set<NODE> nodes = flat.getSetConstraintForExpression(node);
		if (nodes == null) {
			return null;
		}

		return nodes.stream().map(n -> n.getTerm()).collect(Collectors.toSet());
	}
}
