/*
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 *
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.variableassignment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IValuation;

/**
 * The content provider for the VariableAssignment
 *
 * @author Stefan Wissert
 *
 */
public class VariableAssignmentContentProvider implements ITreeContentProvider {

	private IValuation mValuation;
	private final List<VarAssNode> mInternalList;

	public VariableAssignmentContentProvider() {
		mInternalList = new ArrayList<VarAssNode>();
	}

	@Override
	public void dispose() {
		mInternalList.clear();
	}

	@Override
	public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
		if (!(viewer instanceof TreeViewer)) {
			return;
		}
		final TreeViewer tv = (TreeViewer) viewer;
		tv.getTree().removeAll();
		mInternalList.clear();
		final Integer index = (Integer) newInput;
		if (mValuation == null || index == null) {
			return;
		}
		final Set<Entry<String, Entry<IBoogieType, List<String>>>> entrySet = mValuation
		        .getValuesForFailurePathIndex(index).getMap().entrySet();
		for (final Entry<String, Entry<IBoogieType, List<String>>> entry : entrySet) {
			if (entry.getValue().getKey() instanceof BoogieArrayType) {
				final VarAssNode parent = new VarAssNode(entry.getKey(), "");
				final ArrayList<VarAssNode> children = new ArrayList<VarAssNode>();
				for (int i = 0; i < entry.getValue().getValue().size(); i++) {
					final VarAssNode child = new VarAssNode(Integer.toString(i), entry.getValue().getValue().get(i));
					child.setParent(parent);
					children.add(child);
				}
				parent.setChildren(children);
				mInternalList.add(parent);
			} else {
				mInternalList.add(new VarAssNode(entry.getKey(), entry.getValue().getValue().get(0)));
			}
		}
	}

	@Override
	public Object[] getElements(final Object inputElement) {
		return mInternalList.toArray();
	}

	@Override
	public Object[] getChildren(final Object parentElement) {
		if (parentElement instanceof VarAssNode) {
			final VarAssNode node = (VarAssNode) parentElement;
			if (node.getChildren() != null) {
				return node.getChildren().toArray();
			}
		}
		return null;
	}

	@Override
	public Object getParent(final Object element) {
		if (element instanceof VarAssNode) {
			final VarAssNode node = (VarAssNode) element;
			if (node.getParent() != null) {
				return node.getParent();
			}
		}
		return null;
	}

	@Override
	public boolean hasChildren(final Object element) {
		if (element instanceof VarAssNode) {
			return ((VarAssNode) element).getChildren() != null;
		}
		return false;
	}

	/**
	 * @return the valuation
	 */
	public IValuation getValuation() {
		return mValuation;
	}

	/**
	 * @param valuation
	 *            the valuation to set
	 */
	public void setValuation(final IValuation valuation) {
		mValuation = valuation;
	}

}
