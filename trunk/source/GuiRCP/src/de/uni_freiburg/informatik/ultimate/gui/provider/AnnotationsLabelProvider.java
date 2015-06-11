package de.uni_freiburg.informatik.ultimate.gui.provider;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.gui.misc.Entry;
import de.uni_freiburg.informatik.ultimate.gui.misc.GroupEntry;

import org.eclipse.jface.viewers.LabelProvider;

/**
 * @author dietsch
 * 
 */
public class AnnotationsLabelProvider extends LabelProvider {

	private static final int MAX_LENGTH = 500;

	@Override
	public String getText(Object element) {
		if (element instanceof IElement) {
			final IElement elem = (IElement) element;
			if (elem.hasPayload()) {
				return getText(elem.getPayload());
			}
		}
		if (element instanceof IPayload) {
			return ((IPayload) element).getName();
		}
		if (element instanceof GroupEntry) {
			return ((GroupEntry) element).getName();
		}
		if (element instanceof Entry) {

			final String name = ((Entry) element).getName();
			final String value = ((Entry) element).getValue();

			String str;

			if (name == null || name.isEmpty()) {
				str = value;
			} else if (value == null || value.isEmpty()) {
				str = name;
			} else if (name.equals(value)) {
				str = name;
			} else {
				str = name + " - " + value;
			}
			return str.length() > MAX_LENGTH ? str.substring(0, MAX_LENGTH) : str;
		}

		return "UNKNOWN ELEMENT";
	}
}
