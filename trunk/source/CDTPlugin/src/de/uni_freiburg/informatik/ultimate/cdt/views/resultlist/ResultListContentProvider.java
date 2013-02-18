/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.resultlist;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

import de.uni_freiburg.informatik.ultimate.cdt.codan.CDTResultStore;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

/**
 * @author Stefan Wissert
 * 
 */
public class ResultListContentProvider implements ITreeContentProvider {

	private List<IResult> internalList;

	public ResultListContentProvider() {
		internalList = new ArrayList<IResult>();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.viewers.IContentProvider#dispose()
	 */
	@Override
	public void dispose() {
		internalList = null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface
	 * .viewers.Viewer, java.lang.Object, java.lang.Object)
	 */
	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (viewer instanceof TreeViewer) {
			TreeViewer tViewer = (TreeViewer) viewer;
			tViewer.getTree().removeAll();
			internalList.clear();

			for (IResult res : CDTResultStore.getResults((String) newInput)) {
				if (res instanceof CounterExampleResult
						|| res instanceof UnprovableResult) {
					internalList.add(res);
				}
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java
	 * .lang.Object)
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		return internalList.toArray();
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		return null;
	}

	@Override
	public Object getParent(Object element) {
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		return false;
	}

}
