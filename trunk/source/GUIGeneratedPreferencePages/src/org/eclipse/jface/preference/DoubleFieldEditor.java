/*
 * Author: Julian Löffler
 * 
 * 
 */
package org.eclipse.jface.preference;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;

/**
 * A field editor for an integer type preference.
 */
public class DoubleFieldEditor extends StringFieldEditor {
	private double minValidValue = 0;

	private double maxValidValue = Double.MAX_VALUE;

	private static final int DEFAULT_TEXT_LIMIT = 10;

	/**
	* Creates a new integer field editor
	*/
	protected DoubleFieldEditor() {
	}

	/**
	 * Creates an integer field editor.
	 *
	 * @param name the name of the preference this field editor works on
	 * @param labelText the label text of the field editor
	 * @param parent the parent of the field editor's control
	 */
	public DoubleFieldEditor(String name, String labelText, Composite parent) {
		this(name, labelText, parent, DEFAULT_TEXT_LIMIT);
	}

	/**
	 * Creates an integer field editor.
	 *
	 * @param name the name of the preference this field editor works on
	 * @param labelText the label text of the field editor
	 * @param parent the parent of the field editor's control
	 * @param textLimit the maximum number of characters in the text.
	 */
	public DoubleFieldEditor(String name, String labelText, Composite parent,
			int textLimit) {
		init(name, labelText);
		setTextLimit(textLimit);
		setEmptyStringAllowed(false);
		setErrorMessage(JFaceResources
				.getString("IntegerFieldEditor.errorMessage"));//$NON-NLS-1$
		createControl(parent);
	}

	/**
	 * Sets the range of valid values for this field.
	 *
	 * @param min the minimum allowed value (inclusive)
	 * @param max the maximum allowed value (inclusive)
	 */
	public void setValidRange(double min, double max) {
		minValidValue = min;
		maxValidValue = max;
		setErrorMessage(JFaceResources.format("IntegerFieldEditor.errorMessageRange", //$NON-NLS-1$
				Double.valueOf(min), Double.valueOf(max)));
	}

	@Override
	protected boolean checkState() {

		Text text = getTextControl();

		if (text == null) {
			return false;
		}

		String numberString = text.getText();
		try {
			double number = Double.parseDouble(numberString);
			if (number >= minValidValue && number <= maxValidValue) {
				clearErrorMessage();
				return true;
			}

			showErrorMessage();
			return false;

		} catch (NumberFormatException e1) {
			showErrorMessage();
		}

		return false;
	}

	@Override
	protected void doLoad() {
		Text text = getTextControl();
		if (text != null) {
			double value = getPreferenceStore().getDouble(getPreferenceName());
			text.setText("" + value);//$NON-NLS-1$
			oldValue = "" + value; //$NON-NLS-1$
		}

	}

	@Override
	protected void doLoadDefault() {
		Text text = getTextControl();
		if (text != null) {
			double value = getPreferenceStore().getDefaultDouble(getPreferenceName());
			text.setText("" + value);//$NON-NLS-1$
		}
		valueChanged();
	}

	@Override
	protected void doStore() {
		Text text = getTextControl();
		if (text != null) {
			Double i = Double.valueOf(text.getText());
			getPreferenceStore().setValue(getPreferenceName(), i.doubleValue());
		}
	}

	/**
	 * Returns this field editor's current value as an double.
	 *
	 * @return the value
	 * @exception NumberFormatException if the <code>String</code> does not
	 *   contain a parsable double
	 */
	public double getDoubleValue() throws NumberFormatException {
		return Double.valueOf(getStringValue()).doubleValue();
	}
}
