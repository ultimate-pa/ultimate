/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.variableassignment;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.result.IValuation;

/**
 * The content provider for the VariableAssignment
 * 
 * @author Stefan Wissert
 * 
 */
public class VariableAssignmentContentProvider implements ITreeContentProvider {

	private IValuation valuation;

	private ArrayList<VarAssNode> internalList;

	public VariableAssignmentContentProvider() {
		internalList = new ArrayList<VarAssNode>();
	}

	@Override
	public void dispose() {
		internalList.clear();
	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (viewer instanceof TreeViewer) {
			TreeViewer tv = (TreeViewer) viewer;
			tv.getTree().removeAll();
			internalList.clear();

			Integer index = (Integer) newInput;
			if (valuation != null && index != null) {
				for (Entry<String, SimpleEntry<IType, List<String>>> entry : valuation
						.getValuesForFailurePathIndex(index).entrySet()) {
					if (entry.getValue().getKey() instanceof ArrayType) {
						VarAssNode parent = new VarAssNode(entry.getKey(), "");
						ArrayList<VarAssNode> children = new ArrayList<VarAssNode>();
						for (int i = 0; i < entry.getValue().getValue().size(); i++) {
							VarAssNode child = new VarAssNode(
									Integer.toString(i), entry.getValue()
											.getValue().get(i));
							child.setParent(parent);
							children.add(child);
						}
						parent.setChildren(children);
						internalList.add(parent);
					} else {
						internalList.add(new VarAssNode(entry.getKey(), entry
								.getValue().getValue().get(0)));
					}
				}
			}
		}
	}

	@Override
	public Object[] getElements(Object inputElement) {
		return internalList.toArray();
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof VarAssNode) {
			VarAssNode node = (VarAssNode) parentElement;
			if (node.getChildren() != null) {
				return node.getChildren().toArray();
			}
		}
		return null;
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof VarAssNode) {
			VarAssNode node = (VarAssNode) element;
			if (node.getParent() != null) {
				return node.getParent();
			}
		}
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof VarAssNode) {
			return ((VarAssNode) element).getChildren() != null;
		}
		return false;
	}

	/**
	 * @return the valuation
	 */
	public IValuation getValuation() {
		return valuation;
	}

	/**
	 * @param valuation
	 *            the valuation to set
	 */
	public void setValuation(IValuation valuation) {
		this.valuation = valuation;
	}

}
