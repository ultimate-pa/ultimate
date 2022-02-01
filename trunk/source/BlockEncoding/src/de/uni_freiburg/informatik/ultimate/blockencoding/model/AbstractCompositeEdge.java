/*
 * Copyright (C) 2013-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Basic abstract class for composite edges (Conjunction or Disjunction),
 * because their behavior is here exactly the same.
 * 
 * @author Stefan Wissert
 * 
 */
public abstract class AbstractCompositeEdge implements ICompositeEdge {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This edge (exactly the formula of this edge) is the left side of the
	 * operation
	 */
	protected IMinimizedEdge leftEdge;

	/**
	 * This edge (exactly the formula of this edge) is the right side of the
	 * operation
	 */
	protected IMinimizedEdge rightEdge;

	protected int mContainedDisjunctions;

	protected Payload payload;

	private int counter;

	private HashSet<IMinimizedEdge> containedEdges;

	private HashSet<IProgramVar> usedVariables;

	/**
	 * Constructs a conjunction which is build up on left and right. <br>
	 * Conjunction = left /\ right
	 * 
	 * @param left
	 *            the left side of the conjunction
	 * @param right
	 *            the right side of the conjunction
	 */
	protected AbstractCompositeEdge(IMinimizedEdge left, IMinimizedEdge right) {
		containedEdges = initContainedEdges(left, right);
		leftEdge = left;
		counter = counter + left.getElementCount();
		rightEdge = right;
		counter = counter + right.getElementCount();
		payload = new Payload();
		// update the contained disjunctions
		if (left instanceof AbstractCompositeEdge) {
			mContainedDisjunctions = ((AbstractCompositeEdge) left)
					.getContainedDisjunctions();
		}
		if (right instanceof AbstractCompositeEdge) {
			mContainedDisjunctions += ((AbstractCompositeEdge) right)
					.getContainedDisjunctions();
		}
		usedVariables = new HashSet<IProgramVar>();
		usedVariables.addAll(left.getDifferentVariables());
		usedVariables.addAll(right.getDifferentVariables());
		EncodingStatistics.setMaxMinDiffVariablesInOneEdge(usedVariables
				.size());
	}

	/**
	 * This empty constructor is needed to create some edges
	 */
	protected AbstractCompositeEdge() {

	}

	/**
	 * @param left
	 * @param right
	 * @return
	 */
	private HashSet<IMinimizedEdge> initContainedEdges(IMinimizedEdge left,
			IMinimizedEdge right) {
		final HashSet<IMinimizedEdge> conEdges = new HashSet<IMinimizedEdge>();
		if (left.isBasicEdge()) {
			conEdges.add(left);
		} else {
			conEdges.addAll(((AbstractCompositeEdge) left)
					.getContainedEdgesSet());
		}
		if (right.isBasicEdge()) {
			conEdges.add(right);
		} else {
			conEdges.addAll(((AbstractCompositeEdge) right)
					.getContainedEdgesSet());
		}
		return conEdges;
	}

	/**
	 * @return
	 */
	public Set<IMinimizedEdge> getContainedEdgesSet() {
		return containedEdges;
	}

	/**
	 * Old and recursive variant of duplicationOfFormula
	 * 
	 * @param edgeToCheck
	 * @return
	 */
	@SuppressWarnings("unused")
	private boolean duplicationOfFormulaRecursive(IMinimizedEdge edgeToCheck) {
		if (edgeToCheck.isBasicEdge()) {
			return containedEdges.contains(edgeToCheck);
		} else {
			final boolean flag = containedEdges.contains(edgeToCheck);
			if (flag) {
				return true;
			}
		}
		final IMinimizedEdge[] compositeEdges = ((ICompositeEdge) edgeToCheck)
				.getCompositeEdges();
		final boolean left = duplicationOfFormula(compositeEdges[0]);
		final boolean right = duplicationOfFormula(compositeEdges[1]);
		return left || right;
	}

	/**
	 * This method checks whether we duplicate parts of our formula. In general
	 * there should be no duplication, but there exist examples,
	 * BigBranchingExample, where this can happen. If we have a duplication, we
	 * not allow the algorithm to merge them!
	 * 
	 * @param edgeToCheck
	 * @return true if there is a duplication, false if there is no duplication
	 */
	@Override
	public boolean duplicationOfFormula(IMinimizedEdge edgeToCheck) {
		// Instead of using the recursive algorithm we use here Set-Intersection
		// it seems to be a little bit faster, and way more easier to debug.
		if (!edgeToCheck.isBasicEdge()) {
			final HashSet<IMinimizedEdge> interSection = new HashSet<IMinimizedEdge>(
					containedEdges);
			interSection.retainAll(((AbstractCompositeEdge) edgeToCheck)
					.getContainedEdgesSet());

			return !interSection.isEmpty();
		} else {
			return containedEdges.contains(edgeToCheck);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.interfaces.model.
	 * IMinimizedEdge#getSource()
	 */
	@Override
	public MinimizedNode getSource() {
		// the source is the source of the leftSide
		return leftEdge.getSource();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.interfaces.model.
	 * IMinimizedEdge#getTarget()
	 */
	@Override
	public MinimizedNode getTarget() {
		// the target is the target of the rightSide
		return rightEdge.getTarget();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.interfaces.model.
	 * IMinimizedEdge#isBasicEdge()
	 */
	@Override
	public boolean isBasicEdge() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.interfaces.model.
	 * ICompositeEdge#getCompositeEdges()
	 */
	@Override
	public IMinimizedEdge[] getCompositeEdges() {
		return new IMinimizedEdge[] { leftEdge, rightEdge };
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		// StringBuilder sb = new StringBuilder();
		// sb.append(leftEdge.toString());
		// sb.append(" /\\ ");
		// sb.append(rightEdge.toString());
		// return sb.toString();
		return "CompositeEdge";
	}

	@Override
	public void setTarget(MinimizedNode target) {
		rightEdge.setTarget(target);
	}

	@Override
	public void setSource(MinimizedNode source) {
		leftEdge.setSource(source);
	}

	@Override
	public IPayload getPayload() {
		return payload;
	}

	@Override
	public boolean hasPayload() {
		return true;
	}

	@Override
	public void redirectTarget(MinimizedNode target) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void redirectSource(MinimizedNode source) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void disconnectTarget() {
		throw new UnsupportedOperationException();
	}

	@Override
	public void disconnectSource() {
		throw new UnsupportedOperationException();
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	@Override
	public List<IWalkable> getSuccessors() {
		return (List) Arrays.asList(new IMinimizedEdge[] {
				leftEdge, rightEdge });
	}

	@Override
	public int getElementCount() {
		return counter;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.
	 * IMinimizedEdge#isOldVarInvolved()
	 */
	@Override
	public boolean isOldVarInvolved() {
		return leftEdge.isOldVarInvolved() || rightEdge.isOldVarInvolved();
	}

	/**
	 * @return the containedDisjunctions
	 */
	public int getContainedDisjunctions() {
		return mContainedDisjunctions;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.
	 * IMinimizedEdge#getDifferentVariables()
	 */
	@Override
	public Set<IProgramVar> getDifferentVariables() {
		return usedVariables;
	}
	
	@Override
	public IMinimizedEdge getLabel() {
		return this;
	}

}
