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

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.ITree;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.gui.misc.Entry;
import de.uni_freiburg.informatik.ultimate.gui.misc.GroupEntry;
import de.uni_freiburg.informatik.ultimate.gui.misc.TreeViewEntry;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class AnnotationTreeProvider implements ITreeContentProvider {

	private Map<IElement, Object[]> mBuffer;

	@Override
	public Object[] getChildren(final Object parentElement) {
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
	public Object getParent(final Object element) {
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
	public boolean hasChildren(final Object element) {
		if (element instanceof IElement) {
			return generateChildren((IElement) element).length != 0;
		}
		if (element instanceof GroupEntry) {
			return ((GroupEntry) element).getEntries().length != 0;
		}
		return false;
	}

	@Override
	public Object[] getElements(final Object inputElement) {
		return getChildren(inputElement);
	}

	@Override
	public void dispose() {
		// nothing to dispose
	}

	@Override
	public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
		// nothing to do when input changes
	}

	private Object[] generateChildren(final IElement elem) {
		if (mBuffer == null) {
			mBuffer = new HashMap<>();
		}
		Object[] currentBuffer = mBuffer.get(elem);

		if (currentBuffer == null) {
			currentBuffer = generateTree(elem);
			mBuffer.put(elem, currentBuffer);
		}
		return currentBuffer;
	}

	private static Object[] generateTree(final IElement elem) {

		final List<Object> rtr = new ArrayList<>();

		final GroupEntry elementGroup = createIElementGroup(elem);
		rtr.add(elementGroup);

		if (elem.hasPayload()) {
			final IPayload payload = elem.getPayload();
			final GroupEntry annotationGroup = new GroupEntry("IPayload.Annotation", null);
			rtr.add(annotationGroup);

			for (final Map.Entry<String, IAnnotations> outer : payload.getAnnotations().entrySet()) {
				annotationGroup.addEntry(convertEntry(outer.getKey(), outer.getValue(), annotationGroup));
			}
		}
		return rtr.toArray();
	}

	private static GroupEntry createIElementGroup(final IElement elem) {
		final GroupEntry elementGroup = new GroupEntry("IElement", null);
		final Object inspectionTarget;
		if (elem instanceof VisualizationNode) {
			inspectionTarget = ((VisualizationNode) elem).getBacking();
		} else if (elem instanceof VisualizationEdge) {
			inspectionTarget = ((VisualizationEdge) elem).getBacking();
		} else {
			inspectionTarget = elem;
		}

		elementGroup.addEntry(new Entry("HashCode", String.valueOf(inspectionTarget.hashCode()), elementGroup));
		elementGroup.addEntry(
				new Entry("Class", String.valueOf(inspectionTarget.getClass().getSimpleName()), elementGroup));
		addVisualizableFieldsAndMethods(elementGroup, inspectionTarget);
		return elementGroup;
	}

	private static void addVisualizableFieldsAndMethods(final GroupEntry elementGroup, final Object inspectionTarget) {
		final Field[] fields = getFields(inspectionTarget);
		for (final Field field : fields) {
			if (!field.isAnnotationPresent(Visualizable.class)) {
				continue;
			}
			try {
				field.setAccessible(true);
				final Object value = field.get(inspectionTarget);
				elementGroup.addEntry(convertEntry(field.getName(), value, elementGroup));
			} catch (final Exception ex) {
				// we ignore all exceptions during retrieval
			}
		}

		final Method[] methods = getMethods(inspectionTarget);
		for (final Method method : methods) {
			if (!method.isAnnotationPresent(Visualizable.class)) {
				continue;
			}
			try {
				method.setAccessible(true);
				final Object value = method.invoke(inspectionTarget);
				elementGroup.addEntry(convertEntry(method.getName(), value, elementGroup));
			} catch (final Exception ex) {
				// we ignore all exceptions during retrieval
			}
		}
	}

	private static Field[] getFields(final Object inspectionTarget) {
		final List<Field> rtr = new ArrayList<>();

		Class<?> clazz = inspectionTarget.getClass();
		while (clazz != null) {
			rtr.addAll(Arrays.asList(clazz.getDeclaredFields()));
			clazz = clazz.getSuperclass();
		}

		return rtr.toArray(new Field[rtr.size()]);
	}

	private static Method[] getMethods(final Object inspectionTarget) {
		final List<Method> rtr = new ArrayList<>();

		Class<?> clazz = inspectionTarget.getClass();
		while (clazz != null) {
			rtr.addAll(Arrays.asList(clazz.getDeclaredMethods()));
			clazz = clazz.getSuperclass();
		}

		return rtr.toArray(new Method[rtr.size()]);
	}

	@SuppressWarnings("unchecked")
	private static TreeViewEntry convertEntry(final String name, final Object value, final GroupEntry parent) {
		if (value instanceof AnnotatedTerm) {
			final AnnotatedTerm form = (AnnotatedTerm) value;
			final GroupEntry group = new GroupEntry(name + " - annotation", parent);
			for (int i = 0; i < form.getAnnotations().length; i++) {
				group.addEntry(convertEntry(String.valueOf(i), form.getAnnotations()[i], group));
			}
			group.addEntry(convertEntry("subform", form.getSubterm(), group));
			return group;
		}
		if (value instanceof ApplicationTerm) {
			final ApplicationTerm form = (ApplicationTerm) value;
			final GroupEntry group = new GroupEntry(name + " - " + form.getFunction(), parent);
			for (int i = 0; i < form.getParameters().length; i++) {
				group.addEntry(convertEntry(String.valueOf(i), form.getParameters()[i], group));
			}
			return group;
		}
		if (value instanceof LetTerm) {
			final LetTerm form = (LetTerm) value;
			final GroupEntry group = new GroupEntry(name + " - let", parent);
			group.addEntry(convertEntry(Arrays.toString(form.getVariables()), form.getValues(), group));
			group.addEntry(convertEntry("subform", form.getSubTerm(), group));
			return group;
		}
		if (value instanceof QuantifiedFormula) {
			final QuantifiedFormula form = (QuantifiedFormula) value;
			final String quant = form.getQuantifier() == QuantifiedFormula.FORALL ? "forall" : "exists";
			final GroupEntry group = new GroupEntry(name + " - " + quant, parent);
			for (final TermVariable v : form.getVariables()) {
				group.addEntry(convertEntry("var", v, group));
			}
			group.addEntry(convertEntry("subform", form.getSubformula(), group));
			return group;
		}
		if (value instanceof ILocation) {
			final ILocation loc = (ILocation) value;
			final GroupEntry locGroup = new GroupEntry(name, parent);
			locGroup.addEntry(new Entry("Type", loc.getClass().getSimpleName(), locGroup));
			locGroup.addEntry(new Entry("Source Info", loc.toString(), locGroup));
			locGroup.addEntry(new Entry("Filename", loc.getFileName(), locGroup));
			locGroup.addEntry(new Entry("Start Line Number", Integer.toString(loc.getStartLine()), locGroup));
			locGroup.addEntry(new Entry("Start Column Number", Integer.toString(loc.getStartColumn()), locGroup));
			locGroup.addEntry(new Entry("End Line Number", Integer.toString(loc.getEndLine()), locGroup));
			locGroup.addEntry(new Entry("End Column Number", Integer.toString(loc.getEndColumn()), locGroup));
			addVisualizableFieldsAndMethods(locGroup, value);
			return locGroup;
		}
		if (value instanceof ITree) {
			return convertITreeEntry(String.valueOf(value), (ITree) value, parent);
		}
		if (value instanceof IAnnotations) {
			final Map<String, Object> mapping = ((IAnnotations) value).getAnnotationsAsMap();
			final GroupEntry group = new GroupEntry(name, parent);
			group.addEntry(convertEntry("toString", String.valueOf(value), parent));
			for (final Map.Entry<String, Object> attrib : mapping.entrySet()) {
				group.addEntry(convertEntry(attrib.getKey(), mapping.get(attrib.getKey()), group));
			}
			addVisualizableFieldsAndMethods(group, value);
			return group;
		}

		if (value instanceof Map) {
			final GroupEntry group = new GroupEntry(name, parent);
			for (final Map.Entry<Object, Object> e : ((Map<Object, Object>) value).entrySet()) {
				group.addEntry(convertEntry(e.getKey().toString(), e.getValue(), group));
			}
			return group;
		}
		if (value instanceof Collection) {
			final GroupEntry group = new GroupEntry(name, parent);
			int cnt = 0;
			for (final Object obj : (Collection<?>) value) {
				cnt++;
				group.addEntry(convertEntry(String.valueOf(cnt), obj, group));
			}
			return group;
		}
		if (value instanceof Object[]) {
			final GroupEntry group = new GroupEntry(name, parent);
			final Object[] arr = (Object[]) value;
			for (int i = 0; i < arr.length; i++) {
				group.addEntry(convertEntry(String.valueOf(i), arr[i], group));
			}
			return group;
		}

		return new Entry(name, String.valueOf(value), parent);
	}

	private static TreeViewEntry convertITreeEntry(final String name, final ITree value, final GroupEntry parent) {
		final List<IWalkable> children = value.getSuccessors();
		if (children != null && !children.isEmpty()) {
			final GroupEntry group = new GroupEntry(name, parent);
			for (final IWalkable child : children) {
				if (child instanceof ITree) {
					group.addEntry(convertITreeEntry(child.toString(), (ITree) child, group));
				}
			}
			return group;
		}
		return new Entry(name, String.valueOf(value), parent);
	}
}
