/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.locationtrace;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;

/**
 * @author Stefan Wissert
 * 
 */
public class LocationTraceContentProvider implements ITreeContentProvider {

	private List<ILocation> originalFailurePath;

	private List<TraceNode> internalList;

	private HashMap<ILocation, Integer> locationIteration;


	/**
	 * The default Constructor.
	 */
	public LocationTraceContentProvider() {
		internalList = new ArrayList<TraceNode>();
		locationIteration = new HashMap<ILocation, Integer>();
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
			locationIteration.clear();
			TreeViewer tv = (TreeViewer) viewer;
			internalList.clear();
			tv.getTree().removeAll();
			// if the selected item in the TreeView is a CounterExample
			// -> we put them in the LocationStack (Tree)
			if (newInput instanceof CounterExampleResult) {
				originalFailurePath = ((CounterExampleResult) newInput)
						.getFailurePath();
				internalList = compressFailurePath(originalFailurePath);
				for (TraceNode tn : internalList) {
					if (locationIteration.containsKey(tn.getLocation())) {
						int temp = locationIteration.get(tn.getLocation());
						locationIteration.put(tn.getLocation(), temp + 1);
						tn.setIteration(temp + 1);
					} else {
						locationIteration.put(tn.getLocation(), 1);
						tn.setIteration(1);
					}
				}
			}
		}
	}

	/**
	 * We need this because, it is often the case that we have double locations
	 * in the failure path, which are not for representing it in the
	 * LocationTrace. This is not a failure from the model checker furthermore
	 * it is because sometimes we need more Boogie-Statements to express one
	 * C-Statement.
	 * 
	 * @param failurePath
	 *            the original FailurePath
	 * @return the reduced failure path
	 */
	private List<TraceNode> compressFailurePath(List<ILocation> failurePath) {
		ArrayList<TraceNode> newList = new ArrayList<TraceNode>();
		ILocation actualLocation = null;
		int counter = 0;
		int counterv2 = 0;
		for (ILocation loc : failurePath) {
			if (loc instanceof CACSLLocation) {
				if (!loc.equals(actualLocation)) {
					TraceNode tn = new TraceNode(loc, counterv2, counter);
					newList.add(tn);
					actualLocation = loc;
					counterv2++;
				}
			}
			counter++;
		}
		return newList;
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
