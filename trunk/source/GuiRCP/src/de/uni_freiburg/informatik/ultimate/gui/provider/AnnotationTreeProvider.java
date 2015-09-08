/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DebugGUI plug-in.
 * 
 * The ULTIMATE DebugGUI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DebugGUI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DebugGUI plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DebugGUI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE DebugGUI plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.gui.provider;

import java.io.Console;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
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
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.model.structure.ITree;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;

/**
 * @author dietsch
 */
public class AnnotationTreeProvider implements ITreeContentProvider {

	private Map<IElement, Object[]> mBuffer;

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IElement) {
			return generateChildren((IElement) parentElement);
		}
		if (parentElement instanceof GroupEntry) {
			return ((GroupEntry) parentElement).getEntries();
		}
		if (parentElement instanceof Entry) {
			return null;
		}
		return null;
	}

	@Override
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

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof IElement) {
			return generateChildren((IElement) element).length != 0;
		}
		if (element instanceof GroupEntry) {
			return ((GroupEntry) element).getEntries().length != 0;
		}
		if (element instanceof Entry) {
			return false;
		}
		return false;
	}

	@Override
	public Object[] getElements(Object inputElement) {
		return getChildren(inputElement);
	}

	@Override
	public void dispose() {
		// nothing to dispose
	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		// nothing to do when input changes
	}

	private Object[] generateChildren(IElement elem) {
		if (mBuffer == null) {
			mBuffer = new HashMap<IElement, Object[]>();
		}
		Object[] currentBuffer = mBuffer.get(elem);

		if (currentBuffer == null) {
			currentBuffer = generateTree(elem);
			mBuffer.put(elem, currentBuffer);
		}
		return currentBuffer;
	}

	private Object[] generateTree(IElement elem) {

		final List<Object> rtr = new ArrayList<Object>();

		final GroupEntry elementGroup = createIElementGroup(elem);
		rtr.add(elementGroup);

		if (elem.hasPayload()) {
			IPayload payload = elem.getPayload();

			final GroupEntry payloadGroup = new GroupEntry("IPayload", null);
			rtr.add(payloadGroup);
			payloadGroup.addEntry(new Entry("Name", payload.getName(), elementGroup));
			payloadGroup.addEntry(new Entry("UID", payload.getID().toString(), elementGroup));

			final ILocation loc = payload.getLocation();
			if (loc != null) {
				GroupEntry location = new GroupEntry("IPayload.Location", elementGroup);
				rtr.add(location);
				location.addEntry(new Entry("Source Info", payload.getLocation().toString(), location));
				location.addEntry(new Entry("Filename", payload.getLocation().getFileName(), location));
				location.addEntry(new Entry("Start Line Number",
						Integer.toString(payload.getLocation().getStartLine()), location));
				location.addEntry(new Entry("Start Column Number", Integer.toString(payload.getLocation()
						.getStartColumn()), location));
				location.addEntry(new Entry("End Line Number", Integer.toString(payload.getLocation().getEndLine()),
						location));
				location.addEntry(new Entry("End Column Number",
						Integer.toString(payload.getLocation().getEndColumn()), location));
			}
			final GroupEntry annotation = new GroupEntry("IPayload.Annotation", null);
			rtr.add(annotation);
			for (final String outer : payload.getAnnotations().keySet()) {
				final GroupEntry group = new GroupEntry(outer, annotation);
				final IAnnotations subhash = payload.getAnnotations().get(outer);

				for (final String inner : subhash.getAnnotationsAsMap().keySet()) {
					group.addEntry(convertEntry(inner, subhash.getAnnotationsAsMap().get(inner), group));
				}
				annotation.addEntry(group);
			}
		}
		return rtr.toArray();
	}

	private GroupEntry createIElementGroup(IElement elem) {
		final GroupEntry elementGroup = new GroupEntry("IElement", null);
		elementGroup.addEntry(new Entry("HashCode", String.valueOf(elem.hashCode()), elementGroup));

		final Object inspectionTarget;
		if (elem instanceof VisualizationNode) {
			inspectionTarget = ((VisualizationNode) elem).getBacking();
		} else if (elem instanceof VisualizationEdge) {
			inspectionTarget = ((VisualizationEdge) elem).getBacking();
		} else {
			inspectionTarget = elem;
		}

		final Field[] fields = getFields(inspectionTarget);
		for (final Field field : fields) {
			if (!field.isAnnotationPresent(Visualizable.class)) {
				continue;
			}
			try {
				field.setAccessible(true);
				Object value = field.get(inspectionTarget);
				elementGroup.addEntry(new Entry(field.getName(), String.valueOf(value), elementGroup));
			} catch (Exception ex) {
				ex.printStackTrace();
				// we ignore all exceptions during retrieval
			}
		}
		return elementGroup;
	}

	private Field[] getFields(final Object inspectionTarget) {
		List<Field> rtr = new ArrayList<>();

		Class<?> clazz = inspectionTarget.getClass();
		while (clazz != null) {
			rtr.addAll(Arrays.asList(clazz.getDeclaredFields()));
			clazz = clazz.getSuperclass();
		}

		return rtr.toArray(new Field[rtr.size()]);
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
			group.addEntry(convertEntry(Arrays.toString(form.getVariables()), form.getValues(), group));
			group.addEntry(convertEntry("subform", form.getSubTerm(), group));
			return group;
		}
		if (value instanceof QuantifiedFormula) {
			QuantifiedFormula form = (QuantifiedFormula) value;
			String quant = form.getQuantifier() == QuantifiedFormula.FORALL ? "forall" : "exists";
			GroupEntry group = new GroupEntry(name + " - " + quant, parent);
			for (TermVariable v : form.getVariables()) {
				group.addEntry(convertEntry("var", v, group));
			}
			group.addEntry(convertEntry("subform", form.getSubformula(), group));
			return group;
		}
		if (value instanceof ITree) {
			return convertITreeEntry(String.valueOf(value), (ITree) value, parent);
		}
		if (value instanceof IAnnotations) {
			Map<String, Object> mapping = ((IAnnotations) value).getAnnotationsAsMap();
			GroupEntry group = new GroupEntry(name, parent);
			for (final java.util.Map.Entry<String, Object> attrib : mapping.entrySet()) {
				group.addEntry(convertEntry(attrib.getKey(), mapping.get(attrib.getKey()), group));
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
				cnt++;
				group.addEntry(convertEntry(String.valueOf(cnt), o, group));
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
		if (children != null && !children.isEmpty()) {
			GroupEntry group = new GroupEntry(name, parent);
			for (IWalkable child : children) {
				if (child instanceof ITree) {
					group.addEntry(convertITreeEntry(child.toString(), (ITree) child, group));
				}
			}
			return group;
		} else {
			return new Entry(name, String.valueOf(value), parent);
		}
	}
}
