/**
 * 
 */
package local.stalin.gui.provider;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import local.stalin.gui.misc.Entry;
import local.stalin.gui.misc.GroupEntry;
import local.stalin.gui.misc.TreeViewEntry;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.FletFormula;
import local.stalin.logic.Formula;
import local.stalin.logic.LetFormula;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.TermVariable;
import local.stalin.model.IAnnotations;
import local.stalin.model.IPayload;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

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
		if(element instanceof IPayload){
			return null;
		}
		if(element instanceof GroupEntry){
			return ((GroupEntry)element).getParent();
		}
		if(element instanceof Entry){
			return ((Entry)element).getParent();
		}
		return null;
	}

	public boolean hasChildren(Object element) {
		if(element instanceof IPayload){
			return generateChildren((IPayload)element).length!=0;
		}
		if(element instanceof GroupEntry){
			return ((GroupEntry)element).getEntries().length!=0;
		}
		if(element instanceof Entry){
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

	private Object[] generateChildren(IPayload node){
		ArrayList<Object> returnObj = new ArrayList<Object>();
		GroupEntry general = new GroupEntry("General",null);
//		general.addEntry(new Entry("Depth",Integer.toString(node.getDepth()),general));
		general.addEntry(new Entry("Name",node.getName(),general));
		general.addEntry(new Entry("UID",node.getID().toString(),general));
		GroupEntry location = new GroupEntry("Location",general);
		general.addEntry(location);
		location.addEntry(new Entry("Filename",node.getLocation().getFileName(),location));
		location.addEntry(new Entry("Package",node.getLocation().getPackage(),location));
		location.addEntry(new Entry("Start Line Number",Integer.toString(node.getLocation().getStartLine()),location));
		location.addEntry(new Entry("Start Column Number",Integer.toString(node.getLocation().getStartColumn()),location));
		location.addEntry(new Entry("End Line Number",Integer.toString(node.getLocation().getEndLine()),location));
		location.addEntry(new Entry("End Column Number",Integer.toString(node.getLocation().getEndColumn()),location));
		GroupEntry annotation = new GroupEntry("Annotations",null);
	
		for(String outer: node.getAnnotations().keySet()){
			GroupEntry group = new GroupEntry(outer,annotation);
			IAnnotations subhash = node.getAnnotations().get(outer); 
			
			for(String inner: subhash.getAnnotationsAsMap().keySet()){
				group.addEntry(convertEntry(inner, subhash.getAnnotationsAsMap().get(inner), group));
			}
			annotation.addEntry(group);
			
		}
		returnObj.add(general);
		returnObj.add(annotation);
		return returnObj.toArray();
	}

	@SuppressWarnings("unchecked")
	private TreeViewEntry convertEntry(String name, Object value, GroupEntry parent) {
		if (value instanceof Map) {
			GroupEntry group = new GroupEntry(name, parent);
			for (Map.Entry<Object,Object> e: ((Map<Object,Object>) value).entrySet()) {
				group.addEntry(convertEntry(e.getKey().toString(), e.getValue(), group));
			}
			return group;
		}
		if (value instanceof Collection) {
			GroupEntry group = new GroupEntry(name, parent);
			int cnt = 0;
			for (Object o: (Collection) value) {
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
		if (value instanceof IAnnotations) {
			Map<String,Object> mapping = 
								((IAnnotations) value).getAnnotationsAsMap();
			GroupEntry group = new GroupEntry(name, parent);
			for (String attrib : mapping.keySet()) {
				group.addEntry(convertEntry(attrib,mapping.get(attrib),group));
			}
			return group;
		}
		if (value instanceof QuantifiedFormula) {
			QuantifiedFormula form = (QuantifiedFormula) value;
			String quant = form.getQuantifier() == QuantifiedFormula.FORALL ? "forall" : "exists";
			GroupEntry group = new GroupEntry(name + " - " + quant, parent);
			for (TermVariable v : form.getVariables())
				group.addEntry(convertEntry("var", v, group));
			group.addEntry(convertEntry("subform", form.getSubformula(), group));
			if (form.getTriggers().length > 0) {
				if (form.getTriggers().length == 1) {
					group.addEntry(convertEntry("trigger", form.getTriggers()[0], group));
				} else {
					group.addEntry(convertEntry("triggers", form.getTriggers(), group));
				}
			}
			return group;
		}
		if (value instanceof ConnectedFormula) {
			ConnectedFormula form = (ConnectedFormula) value;
			GroupEntry group = new GroupEntry(name + " - "+ form.getConnectorName(), parent);
			group.addEntry(convertEntry("1", form.getLhs(), group));
			int i = 2;
			Formula rhs = form.getRhs();
			while (rhs instanceof ConnectedFormula
				   && ((ConnectedFormula)rhs).getConnector() == form.getConnector()) {
				ConnectedFormula cf = (ConnectedFormula) rhs;
				group.addEntry(convertEntry(String.valueOf(i++), cf.getLhs(), group));
				rhs = cf.getRhs();
			}
			group.addEntry(convertEntry(String.valueOf(i++), rhs, group));
			return group;
		}
		if (value instanceof NegatedFormula) {
			NegatedFormula form = (NegatedFormula) value;
			GroupEntry group = new GroupEntry(name + " - not", parent);
			group.addEntry(convertEntry("1", form.getSubFormula(), group));
			return group;
		}
		if (value instanceof LetFormula) {
			LetFormula form = (LetFormula) value;
			GroupEntry group = new GroupEntry(name + " - let", parent);
			group.addEntry(convertEntry(form.getVariable().toString(), form.getValue(), group));
			group.addEntry(convertEntry("subform", form.getSubFormula(), group));
			return group;
		}
		if (value instanceof FletFormula) {
			FletFormula form = (FletFormula) value;
			GroupEntry group = new GroupEntry(name + " - flet", parent);
			group.addEntry(convertEntry(form.getVariable().toString(), form.getValue(), group));
			group.addEntry(convertEntry("subform", form.getSubFormula(), group));
			return group;
		}
		return new Entry(name, String.valueOf(value), parent);
	}

}
