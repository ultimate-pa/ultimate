/*
 * Copyright (C) 2018 Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
/**
 * The implication vertex is part of the {@link ImplicationGraph} and stores a predicate Descendants are implied
 * predicates and ancestors imply the predicate.
 *
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class ImplicationVertex<T extends IPredicate>{
	private final T mPredicate;
	private final Set<ImplicationVertex<T>> mChildren;
	private final Set<ImplicationVertex<T>> mParents;
	private Set<ImplicationVertex<T>> mDescendants;
	private Set<ImplicationVertex<T>> mAncestors;

	public ImplicationVertex(final T predicate, final Set<ImplicationVertex<T>> children,
			final Set<ImplicationVertex<T>> parents) {
		mPredicate = predicate;
		mChildren = children;
		mParents = parents;
		mDescendants = new HashSet<>();
		mAncestors = new HashSet<>();
		transitiveReductionAfterAdding();
		updateTransitiveClosure();
	}

	private void updateTransitiveClosure() {
		mDescendants.addAll(mChildren);
		for(ImplicationVertex<T> child : mChildren) {
			mDescendants.addAll(child.getDescendants());
		}
		mAncestors.addAll(mParents);
		for(ImplicationVertex<T> parent : mParents) {
			mAncestors.addAll(parent.getAncestors());
		}
		for(ImplicationVertex<T> descendant : mDescendants) {
			descendant.addAncestor(this);
		}
		for(ImplicationVertex<T> ancestor : mAncestors) {
			ancestor.addDescendant(this);
		}
	}

	/**
	 * remove edges due to transitive reduction
	 */
	protected void transitiveReductionAfterAdding() {
		for (final ImplicationVertex<T> parent : mParents) {
			for (final ImplicationVertex<T> child : mChildren) {
				if (((ImplicationVertex<T>) parent).getChildren().contains(child)) {
					((ImplicationVertex<T>) parent).removeChild(child);
					((ImplicationVertex<T>) child).removeParent(parent);
				}
				((ImplicationVertex<T>) child).addParent(this);
			}
			((ImplicationVertex<T>) parent).addChild(this);
		}
	}

	@Override
	public String toString() {
		final Set<T> c = new HashSet<>();
		mChildren.forEach(child -> c.add(((ImplicationVertex<T>) child).mPredicate));
		return String.valueOf(mPredicate.toString()) + "-> " + c.toString();
	}
	
	/**
	 * @return every predicate that is implied by mPredicate (mPredicate is not included)
	 */
	public Set<ImplicationVertex<T>> getDescendants(){
		return mDescendants;
	}
	
	/**
	 * @return every predicate that implies mPredicate (mPredicate is not included)
	 */
	public Set<ImplicationVertex<T>> getAncestors(){
		return mAncestors;
	}
	
	protected Set<ImplicationVertex<T>> getChildren() {
		return mChildren;
	}

	protected Set<ImplicationVertex<T>> getParents() {
		return mParents;
	}
	
	public boolean addAncestor(ImplicationVertex<T> ancestor) {
		return mAncestors.add(ancestor);
	}
	
	public boolean addDescendant(ImplicationVertex<T> descendant) {
		return mDescendants.add(descendant);
	}

	protected boolean addChild(final ImplicationVertex<T> child) {
		return mChildren.add(child);
	}

	protected boolean addParent(final ImplicationVertex<T> parent) {
		return mParents.add(parent);
	}

	protected boolean removeChild(final ImplicationVertex<T> child) {
		return mChildren.remove(child);
	}

	protected boolean removeParent(final ImplicationVertex<T> parent) {
		return mParents.remove(parent);
	}

	public T getPredicate() {
		return mPredicate;
	}
}