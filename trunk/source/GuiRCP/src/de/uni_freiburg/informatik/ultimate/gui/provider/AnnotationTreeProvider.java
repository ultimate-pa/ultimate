/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.gui.provider;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import de.uni_freiburg.informatik.ultimate.gui.misc.Entry;
import de.uni_freiburg.informatik.ultimate.gui.misc.GroupEntry;
import de.uni_freiburg.informatik.ultimate.gui.misc.TreeViewEntry;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.structure.ITree;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;

/**
 * @author dietsch
 * 
 */
public class AnnotationTreeProvider implements ITreeContentProvider {

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IPayload) {
			return generateChildren((IPayload) parentElement);
		}
		if (parentElement instanceof GroupEntry) {
			return ((GroupEntry) parentElement).getEntries();
		}
		if (parentElement instanceof Entry) {
			return null;
		}
		return null;
	}

	public Object getParent(Object element) {
		if (element instanceof IPayload) {
			return null;
		}
		if (element instanceof GroupEntry) {
			return ((GroupEntry) element).getParent();
		}
		if (element instanceof Entry) {
			return ((Entry) element).getParent();
		}
		return null;
	}

	public boolean hasChildren(Object element) {
		if (element instanceof IPayload) {
			return generateChildren((IPayload) element).length != 0;
		}
		if (element instanceof GroupEntry) {
			return ((GroupEntry) element).getEntries().length != 0;
		}
		if (element instanceof Entry) {
			return false;
		}
		return false;
	}

	public Object[] getElements(Object inputElement) {
		return getChildren(inputElement);
	}

	public void dispose() {

	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {

	}

	private Map<IPayload,Object[]> mBuffer;

	private Object[] generateChildren(IPayload node) {
		if(mBuffer == null){
			mBuffer = new HashMap<IPayload,Object[]>();
		}
		
		Object[] currentBuffer = mBuffer.get(node);
		
		if (currentBuffer == null) {
			ArrayList<Object> returnObj = new ArrayList<Object>();
			GroupEntry general = new GroupEntry("General", null);
			// general.addEntry(new
			// Entry("Depth",Integer.toString(node.getDepth()),general));
			general.addEntry(new Entry("Name", node.getName(), general));
			general.addEntry(new Entry("UID", node.getID().toString(), general));
			GroupEntry location = new GroupEntry("Location", general);
			general.addEntry(location);
			location.addEntry(new Entry("Source Info", node.getLocation().toString(), location));
			location.addEntry(new Entry("Filename", node.getLocation().getFileName(), location));
			location.addEntry(new Entry("Start Line Number", Integer.toString(node.getLocation().getStartLine()),
					location));
			location.addEntry(new Entry("Start Column Number", Integer.toString(node.getLocation().getStartColumn()),
					location));
			location.addEntry(new Entry("End Line Number", Integer.toString(node.getLocation().getEndLine()), location));
			location.addEntry(new Entry("End Column Number", Integer.toString(node.getLocation().getEndColumn()),
					location));
			GroupEntry annotation = new GroupEntry("Annotations", null);

			for (String outer : node.getAnnotations().keySet()) {
				GroupEntry group = new GroupEntry(outer, annotation);
				IAnnotations subhash = node.getAnnotations().get(outer);

				for (String inner : subhash.getAnnotationsAsMap().keySet()) {
					group.addEntry(convertEntry(inner, subhash.getAnnotationsAsMap().get(inner), group));
				}
				annotation.addEntry(group);

			}
			returnObj.add(general);
			returnObj.add(annotation);
			currentBuffer = returnObj.toArray();
			mBuffer.put(node, currentBuffer);
		}
		return currentBuffer;
	}

	@SuppressWarnings("unchecked")
	private TreeViewEntry convertEntry(String name, Object value, GroupEntry parent) {
		if (value instanceof AnnotatedTerm) {
			AnnotatedTerm form = (AnnotatedTerm) value;
			GroupEntry group = new GroupEntry(name + " - annotation", parent);
			for (int i = 0; i < form.getAnnotations().length; i++) {
				group.addEntry(convertEntry(String.valueOf(i), form.getAnnotations()[i], group));
			}
			group.addEntry(convertEntry("subform", form.getSubterm(), group));
			return group;
		}
		if (value instanceof ApplicationTerm) {
			ApplicationTerm form = (ApplicationTerm) value;
			GroupEntry group = new GroupEntry(name + " - " + form.getFunction(), parent);
			for (int i = 0; i < form.getParameters().length; i++) {
				group.addEntry(convertEntry(String.valueOf(i), form.getParameters()[i], group));
			}
			return group;
		}
		if (value instanceof LetTerm) {
			LetTerm form = (LetTerm) value;
			GroupEntry group = new GroupEntry(name + " - let", parent);
			group.addEntry(convertEntry(form.getVariables().toString(), form.getValues(), group));
			group.addEntry(convertEntry("subform", form.getSubTerm(), group));
			return group;
		}
		if (value instanceof QuantifiedFormula) {
			QuantifiedFormula form = (QuantifiedFormula) value;
			String quant = form.getQuantifier() == QuantifiedFormula.FORALL ? "forall" : "exists";
			GroupEntry group = new GroupEntry(name + " - " + quant, parent);
			for (TermVariable v : form.getVariables())
				group.addEntry(convertEntry("var", v, group));
			group.addEntry(convertEntry("subform", form.getSubformula(), group));
			return group;
		}
		if (value instanceof ITree) {
			return convertITreeEntry(String.valueOf(value), (ITree) value, parent);
		}
		if (value instanceof IAnnotations) {
			Map<String, Object> mapping = ((IAnnotations) value).getAnnotationsAsMap();
			GroupEntry group = new GroupEntry(name, parent);
			for (String attrib : mapping.keySet()) {
				group.addEntry(convertEntry(attrib, mapping.get(attrib), group));
			}
			return group;
		}

		if (value instanceof Map) {
			GroupEntry group = new GroupEntry(name, parent);
			for (Map.Entry<Object, Object> e : ((Map<Object, Object>) value).entrySet()) {
				group.addEntry(convertEntry(e.getKey().toString(), e.getValue(), group));
			}
			return group;
		}
		if (value instanceof Collection) {
			GroupEntry group = new GroupEntry(name, parent);
			int cnt = 0;
			for (Object o : (Collection<?>) value) {
				group.addEntry(convertEntry(String.valueOf(cnt++), o, group));
			}
			return group;
		}
		if (value instanceof Object[]) {
			GroupEntry group = new GroupEntry(name, parent);
			Object[] arr = (Object[]) value;
			for (int i = 0; i < arr.length; i++) {
				group.addEntry(convertEntry(String.valueOf(i), arr[i], group));
			}
			return group;
		}

		return new Entry(name, String.valueOf(value), parent);
	}

	private TreeViewEntry convertITreeEntry(String name, ITree value, GroupEntry parent) {
		List<IWalkable> children = value.getSuccessors();
		if (children != null && children.size() > 0) {
			GroupEntry group = new GroupEntry(name, parent);
			for (IWalkable child : children) {
				if (child instanceof ITree) {
					group.addEntry(convertITreeEntry(child.toString(), (ITree)child, group));
				}
			}
			return group;
		} else {
			return new Entry(name, String.valueOf(value), parent);
		}
	}
}
