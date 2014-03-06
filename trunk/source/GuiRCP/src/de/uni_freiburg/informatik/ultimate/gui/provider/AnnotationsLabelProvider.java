/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.gui.provider;

import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.gui.misc.Entry;
import de.uni_freiburg.informatik.ultimate.gui.misc.GroupEntry;

import org.eclipse.jface.viewers.LabelProvider;

/**
 * @author dietsch
 * 
 */
public class AnnotationsLabelProvider extends LabelProvider {
	public String getText(Object element) {
		if (element instanceof IPayload) {
			return ((IPayload) element).getName();
		}
		if (element instanceof GroupEntry) {
			return ((GroupEntry) element).getName();
		}
		if (element instanceof Entry) {

			String name = ((Entry) element).getName();
			String value = ((Entry) element).getValue();

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
			return str.length() > 500 ? str.substring(0, 500) : str;
		}

		return "UNKNOWN ELEMENT";
	}
}
