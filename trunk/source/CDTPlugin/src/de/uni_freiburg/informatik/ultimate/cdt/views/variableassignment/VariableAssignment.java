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

import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.part.EditorPart;
import org.eclipse.ui.part.ViewPart;

import de.uni_freiburg.informatik.ultimate.cdt.test.TestValuation;
import de.uni_freiburg.informatik.ultimate.cdt.views.locationtrace.LocationTrace;
import de.uni_freiburg.informatik.ultimate.cdt.views.locationtrace.TraceNode;
import de.uni_freiburg.informatik.ultimate.cdt.views.resultlist.ResultList;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;

/**
 * @author Stefan Wissert
 *
 */
public class VariableAssignment extends ViewPart implements ISelectionListener {

	public static String ID = "de.uni_freiburg.informatik.ultimate.cdt.VariableAssignment";

	/**
	 * The underlying JFace component
	 */
	private TreeViewer viewer;

	private VariableAssignmentContentProvider contProv;

	private String actualAllowedInput;

	/*
	 * (non-Javadoc)
	 *
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets .Composite)
	 */
	@Override
	public void createPartControl(final Composite parent) {
		final Tree variableTree = new Tree(parent, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL);
		variableTree.setHeaderVisible(true);
		viewer = new TreeViewer(variableTree);

		final TreeColumn column1 = new TreeColumn(variableTree, SWT.LEFT);
		variableTree.setLinesVisible(true);
		column1.setAlignment(SWT.LEFT);
		column1.setText("Variable-Name");
		column1.setWidth(130);
		final TreeColumn column2 = new TreeColumn(variableTree, SWT.RIGHT);
		column2.setAlignment(SWT.LEFT);
		column2.setText("Assignment");
		column2.setWidth(130);

		viewer.expandAll();

		contProv = new VariableAssignmentContentProvider();
		viewer.setContentProvider(contProv);
		// we have to define an own label provider
		viewer.setLabelProvider(new VariableAssignmentLabelProvider());
		// we add this object as selection listener
		getViewSite().getPage().addSelectionListener(this);
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	@Override
	public void selectionChanged(final IWorkbenchPart part, final ISelection selection) {
		if (selection instanceof ITreeSelection && part instanceof ResultList) {
			final Object first = ((ITreeSelection) selection).getFirstElement();
			if (first instanceof CounterExampleResult) {
				final IEditorPart edPart = getSite().getPage().getActiveEditor();
				actualAllowedInput = edPart.getTitle();
				final CounterExampleResult<?, ?, ?> res = (CounterExampleResult<?, ?, ?>) first;

				if (res.getProgramExecution() != null) {
					// TODO: Implement this right with IProgramExecution and known values for generic
					// contProv.setValuation(res.getValuation());
				} else {
					contProv.setValuation(new TestValuation());
				}
			}
			viewer.getTree().removeAll();
		} else if (selection instanceof ITreeSelection && part instanceof LocationTrace) {
			final Object first = ((ITreeSelection) selection).getFirstElement();
			if (first != null) {
				viewer.setInput(((TraceNode) first).getOriginalIndex());
			}
		} else if (selection instanceof ITextSelection && part instanceof EditorPart) {
			final String text = ((EditorPart) part).getTitle();
			if (!text.equals(actualAllowedInput)) {
				viewer.getTree().removeAll();
			}
		} else if (selection instanceof ITreeSelection && part instanceof CommonNavigator) {
			final CommonNavigator navi = (CommonNavigator) part;
			if (navi.isLinkingEnabled()) {
				if (((ITreeSelection) selection).getFirstElement() != null) {
					final String text = ((ITreeSelection) selection).getFirstElement().toString();
					if (!text.equals(actualAllowedInput)) {
						viewer.getTree().removeAll();
					}
				} else {
					viewer.getTree().removeAll();
				}
			}
		}
	}
}
