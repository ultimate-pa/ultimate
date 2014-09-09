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
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;

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
	 * @see
	 * org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets
	 * .Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		Tree variableTree = new Tree(parent, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL);
		variableTree.setHeaderVisible(true);
		viewer = new TreeViewer(variableTree);

		TreeColumn column1 = new TreeColumn(variableTree, SWT.LEFT);
		variableTree.setLinesVisible(true);
		column1.setAlignment(SWT.LEFT);
		column1.setText("Variable-Name");
		column1.setWidth(130);
		TreeColumn column2 = new TreeColumn(variableTree, SWT.RIGHT);
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
	public void selectionChanged(IWorkbenchPart part, ISelection selection) {
		if (selection instanceof ITreeSelection && part instanceof ResultList) {
			Object first = ((ITreeSelection) selection).getFirstElement();
			if (first instanceof CounterExampleResult) {
				IEditorPart edPart = getSite().getPage().getActiveEditor();
				actualAllowedInput = edPart.getTitle();
				CounterExampleResult res = (CounterExampleResult) first;

				if (res.getProgramExecution() != null) {
					// TODO: Implement this right with IProgramExecution and known values for generic 
					// contProv.setValuation(res.getValuation());
				} else {
					contProv.setValuation(new TestValuation());
				}
			}
			viewer.getTree().removeAll();
		} else if (selection instanceof ITreeSelection && part instanceof LocationTrace) {
			Object first = ((ITreeSelection) selection).getFirstElement();
			if (first != null)
				viewer.setInput(((TraceNode) first).getOriginalIndex());
		} else if (selection instanceof ITextSelection && part instanceof EditorPart) {
			String text = ((EditorPart) part).getTitle();
			if (!text.equals(actualAllowedInput)) {
				viewer.getTree().removeAll();
			}
		} else if (selection instanceof ITreeSelection && part instanceof CommonNavigator) {
			CommonNavigator navi = (CommonNavigator) part;
			if (navi.isLinkingEnabled()) {
				if (((ITreeSelection) selection).getFirstElement() != null) {
					String text = ((ITreeSelection) selection).getFirstElement().toString();
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
