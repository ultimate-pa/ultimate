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
 * A field editor for an double type preference.
 */
public class DoubleFieldEditor extends StringFieldEditor {
	private double mMinValidValue = 0;

	private double mMaxValidValue = Double.MAX_VALUE;

	private static final int DEFAULT_TEXT_LIMIT = 10;

	/**
	 * Creates a new integer field editor
	 */
	protected DoubleFieldEditor() {
	}

	/**
	 * Creates an integer field editor.
	 *
	 * @param name
	 *            the name of the preference this field editor works on
	 * @param labelText
	 *            the label text of the field editor
	 * @param parent
	 *            the parent of the field editor's control
	 */
	public DoubleFieldEditor(final String name, final String labelText, final Composite parent) {
		this(name, labelText, parent, DEFAULT_TEXT_LIMIT);
	}

	/**
	 * Creates an integer field editor.
	 *
	 * @param name
	 *            the name of the preference this field editor works on
	 * @param labelText
	 *            the label text of the field editor
	 * @param parent
	 *            the parent of the field editor's control
	 * @param textLimit
	 *            the maximum number of characters in the text.
	 */
	public DoubleFieldEditor(final String name, final String labelText, final Composite parent, final int textLimit) {
		init(name, labelText);
		setTextLimit(textLimit);
		setEmptyStringAllowed(false);
		setErrorMessage(JFaceResources.getString("IntegerFieldEditor.errorMessage"));//$NON-NLS-1$
		createControl(parent);
	}

	/**
	 * Sets the range of valid values for this field.
	 *
	 * @param min
	 *            the minimum allowed value (inclusive)
	 * @param max
	 *            the maximum allowed value (inclusive)
	 */
	public void setValidRange(final double min, final double max) {
		mMinValidValue = min;
		mMaxValidValue = max;
		final Object[] args = new Object[] { Double.valueOf(min), Double.valueOf(max) };
		setErrorMessage(JFaceResources.format("IntegerFieldEditor.errorMessageRange", args));
	}

	@Override
	protected boolean checkState() {

		final Text text = getTextControl();

		if (text == null) {
			return false;
		}

		final String numberString = text.getText();
		try {
			final double number = Double.parseDouble(numberString);
			if (number >= mMinValidValue && number <= mMaxValidValue) {
				clearErrorMessage();
				return true;
			}

			showErrorMessage();
			return false;

		} catch (final NumberFormatException e1) {
			showErrorMessage();
		}

		return false;
	}

	@Override
	protected void doLoad() {
		final Text text = getTextControl();
		if (text != null) {
			final double value = getPreferenceStore().getDouble(getPreferenceName());
			text.setText("" + value);//$NON-NLS-1$
			oldValue = "" + value; //$NON-NLS-1$
		}

	}

	@Override
	protected void doLoadDefault() {
		final Text text = getTextControl();
		if (text != null) {
			final double value = getPreferenceStore().getDefaultDouble(getPreferenceName());
			text.setText("" + value);//$NON-NLS-1$
		}
		valueChanged();
	}

	@Override
	protected void doStore() {
		final Text text = getTextControl();
		if (text != null) {
			final Double i = Double.valueOf(text.getText());
			getPreferenceStore().setValue(getPreferenceName(), i.doubleValue());
		}
	}

	/**
	 * Returns this field editor's current value as an double.
	 *
	 * @return the value
	 * @exception NumberFormatException
	 *                if the <code>String</code> does not contain a parsable double
	 */
	public double getDoubleValue() throws NumberFormatException {
		return Double.valueOf(getStringValue()).doubleValue();
	}
}
