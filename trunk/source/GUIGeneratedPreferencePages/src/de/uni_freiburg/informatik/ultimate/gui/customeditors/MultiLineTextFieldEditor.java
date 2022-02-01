/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE GUIGeneratedPreferencePages plug-in.
 * 
 * The ULTIMATE GUIGeneratedPreferencePages plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE GUIGeneratedPreferencePages plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE GUIGeneratedPreferencePages plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE GUIGeneratedPreferencePages plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE GUIGeneratedPreferencePages plug-in grant you additional permission
 * to convey the resulting work.
 */
/*******************************************************************************
 * Copyright (c) 2004, 2009 BitMethods Inc and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 * BitMethods Inc - Initial API and implementation
 *******************************************************************************/
package de.uni_freiburg.informatik.ultimate.gui.customeditors;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.FocusAdapter;
import org.eclipse.swt.events.FocusEvent;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * MultiLineTextFieldEditor. Field editor that is same as string field editor
 * but will have the multi line text field for user input.
 * 
 * @noextend This class is not intended to be subclassed by clients.
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class MultiLineTextFieldEditor extends FieldEditor {
	/**
	 * Validation strategy constant (value <code>0</code>) indicating that the
	 * editor should perform validation after every key stroke.
	 * 
	 * @see #setValidateStrategy
	 */
	public static final int VALIDATE_ON_KEY_STROKE = 0;
	
	/**
	 * Validation strategy constant (value <code>1</code>) indicating that the
	 * editor should perform validation only when the text widget loses focus.
	 * 
	 * @see #setValidateStrategy
	 */
	public static final int VALIDATE_ON_FOCUS_LOST = 1;
	
	/**
	 * Text limit constant (value <code>-1</code>) indicating unlimited text
	 * limit and width.
	 */
	public static final int UNLIMITED = -1;
	
	private static final int HEIGHT_HINT = 70;
	private static final int WIDHT_HINT = 100;
	
	/**
	 * The text field, or <code>null</code> if none.
	 */
	private Text mTextField;
	
	/**
	 * Cached valid state.
	 */
	private boolean mIsValid;
	
	/**
	 * Old text value.
	 */
	private String mOldValue;
	private String mCompTitle;
	
	/**
	 * Text limit of text field in characters; initially unlimited.
	 */
	private int mTextLimit = UNLIMITED;
	
	/**
	 * The error message, or <code>null</code> if none.
	 */
	private String mErrorMessage;
	
	/**
	 * Indicates whether the empty string is legal; <code>true</code> by
	 * default.
	 */
	private boolean mEmptyStringAllowed = true;
	
	/**
	 * The validation strategy; <code>VALIDATE_ON_KEY_STROKE</code> by default.
	 */
	private int mValidateStrategy = VALIDATE_ON_KEY_STROKE;
	
	/**
	 * Creates a new string field editor.
	 */
	protected MultiLineTextFieldEditor() {
	}
	
	/**
	 * Creates a string field editor. Use the method <code>setTextLimit</code>
	 * to limit the text.
	 * 
	 * @param name
	 *            the name of the preference this field editor works on
	 * @param labelText
	 *            the label text of the field editor
	 * @param width
	 *            the width of the text input field in characters, or
	 *            <code>UNLIMITED</code> for no limit
	 * @param strategy
	 *            either <code>VALIDATE_ON_KEY_STROKE</code> to perform on the
	 *            fly checking (the default), or
	 *            <code>VALIDATE_ON_FOCUS_LOST</code> to perform validation only
	 *            after the text has been typed in
	 * @param parent
	 *            the parent of the field editor's control
	 * @since 2.0
	 */
	public MultiLineTextFieldEditor(final String name, final String labelText, final int width,
			final int strategy, final Composite parent) {
		init(name, labelText);
		setValidateStrategy(strategy);
		mIsValid = false;
		//TODO: errorMessage maybe wrong
		mErrorMessage = null;
		createControl(parent);
	}
	
	/**
	 * Creates a string field editor. Use the method <code>setTextLimit</code>
	 * to limit the text.
	 * 
	 * @param name
	 *            the name of the preference this field editor works on
	 * @param labelText
	 *            the label text of the field editor
	 * @param width
	 *            the width of the text input field in characters, or
	 *            <code>UNLIMITED</code> for no limit
	 * @param parent
	 *            the parent of the field editor's control
	 */
	public MultiLineTextFieldEditor(final String name, final String labelText, final int width,
			final Composite parent) {
		this(name, labelText, width, VALIDATE_ON_KEY_STROKE, parent);
		mCompTitle = labelText;
	}
	
	/**
	 * Creates a string field editor of unlimited width. Use the method
	 * <code>setTextLimit</code> to limit the text.
	 * 
	 * @param name
	 *            the name of the preference this field editor works on
	 * @param labelText
	 *            the label text of the field editor
	 * @param parent
	 *            the parent of the field editor's control
	 */
	public MultiLineTextFieldEditor(final String name, final String labelText,
			final Composite parent) {
		this(name, labelText, UNLIMITED, parent);
	}
	
	/**
	 * Adjusts the horizontal span of this field editor's basic controls
	 * <p>
	 * Subclasses must implement this method to adjust the horizontal span of
	 * controls so they appear correct in the given number of columns.
	 * </p>
	 * <p>
	 * The number of columns will always be equal to or greater than the value
	 * returned by this editor's <code>getNumberOfControls</code> method.
	 * 
	 * @param numColumns
	 *            the number of columns
	 */
	@Override
	protected void adjustForNumColumns(final int numColumns) {
		final GridData gd = (GridData) mTextField.getLayoutData();
		gd.horizontalSpan = numColumns - 1;
		// We only grab excess space if we have to
		// If another field editor has more columns then
		// we assume it is setting the width.
		gd.grabExcessHorizontalSpace = gd.horizontalSpan == 1;
	}
	
	/**
	 * Checks whether the text input field contains a valid value or not.
	 * 
	 * @return <code>true</code> if the field value is valid, and
	 *         <code>false</code> if invalid
	 */
	boolean checkState() {
		if (mEmptyStringAllowed) {
			return checkStatePostprocessing(true);
		}
		
		if (mTextField == null) {
			return checkStatePostprocessing(false);
		}
		
		final String txt = mTextField.getText();
		
		if (txt == null) {
			return checkStatePostprocessing(false);
		}
		
		return checkStatePostprocessing(containsNonWhiteSpaceCharacter(txt));
	}
	
	private boolean checkStatePostprocessing(final boolean result) {
		if (result) {
			clearErrorMessage();
		} else {
			showErrorMessage(mErrorMessage);
		}
		
		return result;
	}
	
	private static boolean containsNonWhiteSpaceCharacter(final String txt) {
		return txt != null && txt.matches("\\s*");
	}
	
	/**
	 * Fills this field editor's basic controls into the given parent.
	 * <p>
	 * The string field implementation of this <code>FieldEditor</code>
	 * framework method contributes the text field. Subclasses may override but
	 * must call <code>super.doFillIntoGrid</code>.
	 * </p>
	 */
	@Override
	protected void doFillIntoGrid(final Composite parent, final int numColumns) {
		final Label title = new Label(parent, SWT.UP);
		title.setFont(parent.getFont());
		mCompTitle = getLabelText();
		title.setText(mCompTitle);
		title.setLayoutData(new GridData(GridData.VERTICAL_ALIGN_BEGINNING));
		
		mTextField = getTextControl(parent);
		final GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.widthHint = WIDHT_HINT;
		gd.heightHint = HEIGHT_HINT;
		mTextField.setLayoutData(gd);
	}
	
	/**
	 * Initializes this field editor with the preference value from the
	 * preference store.
	 * <p>
	 * Subclasses must implement this method to properly initialize the field
	 * editor.
	 * </p>
	 */
	@Override
	protected void doLoad() {
		if (mTextField != null) {
			final String value = getPreferenceStore().getString(getPreferenceName());
			mTextField.setText(value);
			mOldValue = value;
		}
	}
	
	/**
	 * Initializes this field editor with the default preference value from the
	 * preference store.
	 * <p>
	 * Subclasses must implement this method to properly initialize the field
	 * editor.
	 * </p>
	 */
	@Override
	protected void doLoadDefault() {
		if (mTextField != null) {
			final String value = getPreferenceStore().getDefaultString(
					getPreferenceName());
			mTextField.setText(value);
		}
		valueChanged();
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.preference.FieldEditor#doStore()
	 */
	@Override
	protected void doStore() {
		getPreferenceStore().setValue(getPreferenceName(), mTextField.getText());
	}
	
	/**
	 * Returns the error message that will be displayed when and if an error
	 * occurs.
	 * 
	 * @return the error message, or <code>null</code> if none
	 */
	public String getErrorMessage() {
		return mErrorMessage;
	}
	
	/**
	 * Returns the number of basic controls this field editor consists of.
	 * 
	 * @return the number of controls
	 */
	@Override
	public int getNumberOfControls() {
		return 2;
	}
	
	/**
	 * Returns the field editor's value.
	 * 
	 * @return the current value
	 */
	public String getStringValue() {
		if (mTextField != null) {
			return mTextField.getText();
		}
		return getPreferenceStore().getString(getPreferenceName());
	}
	
	/**
	 * Returns this field editor's text control.
	 * 
	 * @return the text control, or <code>null</code> if no text field is
	 *         created yet
	 */
	Text getTextControl() {
		return mTextField;
	}
	
	/**
	 * Returns this field editor's text control.
	 * <p>
	 * The control is created if it does not yet exist
	 * </p>
	 * 
	 * @param parent
	 *            the parent
	 * @return the text control
	 */
	public Text getTextControl(final Composite parent) {
		if (mTextField == null) {
			mTextField = new Text(parent, SWT.MULTI | SWT.V_SCROLL | SWT.BORDER
					| SWT.WRAP);
			mTextField.setFont(parent.getFont());
			switch (mValidateStrategy) {
				case VALIDATE_ON_KEY_STROKE:
					mTextField.addKeyListener(new KeyAdapterValidateOnKeyStroke());
					mTextField.addFocusListener(new FocusAdapterValidateOnKeyStroke());
					break;
				case VALIDATE_ON_FOCUS_LOST:
					mTextField.addKeyListener(new KeyAdapterValidateOnFocusLost());
					mTextField.addFocusListener(new FocusAdapterValidateOnFocusLost());
					break;
				default:
			}
			mTextField.addDisposeListener(event -> mTextField = null);
			if (mTextLimit > 0) {
				// Only set limits above 0 - see SWT spec
				mTextField.setTextLimit(mTextLimit);
			}
		} else {
			checkParent(mTextField, parent);
		}
		return mTextField;
	}
	
	/**
	 * Returns whether an empty string is a valid value.
	 * 
	 * @return <code>true</code> if an empty string is a valid value, and
	 *         <code>false</code> if an empty string is invalid
	 * @see #setEmptyStringAllowed
	 */
	public boolean isEmptyStringAllowed() {
		return mEmptyStringAllowed;
	}
	
	/**
	 * Returns whether this field editor contains a valid value.
	 * <p>
	 * The default implementation of this framework method returns
	 * <code>true</code>. Subclasses wishing to perform validation should
	 * override both this method and <code>refreshValidState</code>.
	 * </p>
	 * 
	 * @return <code>true</code> if the field value is valid, and
	 *         <code>false</code> if invalid
	 * @see #refreshValidState
	 */
	@Override
	public boolean isValid() {
		return mIsValid;
	}
	
	/**
	 * Refreshes this field editor's valid state after a value change and fires
	 * an <code>IS_VALID</code> property change event if warranted.
	 * <p>
	 * The default implementation of this framework method does nothing.
	 * Subclasses wishing to perform validation should override both this method
	 * and <code>isValid</code>.
	 * </p>
	 */
	@Override
	protected void refreshValidState() {
		mIsValid = checkState();
	}
	
	/**
	 * Sets whether the empty string is a valid value or not.
	 * 
	 * @param bool
	 *            <code>true</code> if the empty string is allowed, and
	 *            <code>false</code> if it is considered invalid
	 */
	public void setEmptyStringAllowed(final boolean bool) {
		mEmptyStringAllowed = bool;
	}
	
	/**
	 * Sets the error message that will be displayed when and if an error
	 * occurs.
	 * 
	 * @param message
	 *            the error message
	 */
	public void setErrorMessage(final String message) {
		mErrorMessage = message;
	}
	
	/**
	 * Sets the focus to this field editor.
	 * <p>
	 * The default implementation of this framework method does nothing.
	 * Subclasses may reimplement.
	 * </p>
	 */
	@Override
	public void setFocus() {
		if (mTextField != null) {
			mTextField.setFocus();
		}
	}
	
	/**
	 * Sets this field editor's value.
	 * 
	 * @param valueIn
	 *            the new value, or <code>null</code> meaning the empty string
	 */
	public void setStringValue(final String valueIn) {
		String value = valueIn;
		if (mTextField != null) {
			if (value == null) {
				value = ""; //$NON-NLS-1$
			}
			mOldValue = mTextField.getText();
			if (!mOldValue.equals(value)) {
				mTextField.setText(value);
				valueChanged();
			}
		}
	}
	
	/**
	 * Sets this text field's text limit.
	 * 
	 * @param limit
	 *            the limit on the number of character in the text input field,
	 *            or <code>UNLIMITED</code> for no limit
	 */
	public void setTextLimit(final int limit) {
		mTextLimit = limit;
		if (mTextField != null) {
			mTextField.setTextLimit(limit);
		}
	}
	
	/**
	 * Sets the strategy for validating the text.
	 * <p>
	 * Calling this method has no effect after <code>createPartControl</code> is
	 * called. Thus this method is really only useful for subclasses to call in
	 * their constructor. However, it has public visibility for backward
	 * compatibility.
	 * </p>
	 * 
	 * @param value
	 *            either <code>VALIDATE_ON_KEY_STROKE</code> to perform on the
	 *            fly checking (the default), or
	 *            <code>VALIDATE_ON_FOCUS_LOST</code> to perform validation only
	 *            after the text has been typed in
	 */
	public void setValidateStrategy(final int value) {
		Assert.isTrue(value == VALIDATE_ON_FOCUS_LOST
				|| value == VALIDATE_ON_KEY_STROKE);
		mValidateStrategy = value;
	}
	
	/**
	 * Shows the error message set via <code>setErrorMessage</code>.
	 */
	public void showErrorMessage() {
		showErrorMessage(mErrorMessage);
	}
	
	/**
	 * Informs this field editor's listener, if it has one, about a change to
	 * the value (<code>VALUE</code> property) provided that the old and new
	 * values are different.
	 * <p>
	 * This hook is <em>not</em> called when the text is initialized (or reset
	 * to the default value) from the preference store.
	 * </p>
	 */
	void valueChanged() {
		setPresentsDefaultValue(false);
		final boolean oldState = mIsValid;
		refreshValidState();
		
		if (mIsValid != oldState) {
			fireStateChanged(IS_VALID, oldState, mIsValid);
		}
		
		final String newValue = mTextField.getText();
		if (!newValue.equals(mOldValue)) {
			fireValueChanged(VALUE, mOldValue, newValue);
			mOldValue = newValue;
		}
	}
	
	@Override
	@SuppressWarnings("squid:S1185")
	// overridden for avoiding compiler hook when nested classes access this method
	protected void clearErrorMessage() {
		super.clearErrorMessage();
	}
	
	/**
	 * {@link KeyAdapter} for {@code VALIDATE_ON_KEY_STROKE}.
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private final class KeyAdapterValidateOnKeyStroke extends KeyAdapter {
		public KeyAdapterValidateOnKeyStroke() {
			// nothing to do, constructor only present to avoid synthetic constructor
		}
		
		@Override
		public void keyPressed(final KeyEvent event) {
			valueChanged();
		}
	}
	
	/**
	 * {@link KeyAdapter} for {@code VALIDATE_ON_FOCUS_LOST}.
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private final class KeyAdapterValidateOnFocusLost extends KeyAdapter {
		public KeyAdapterValidateOnFocusLost() {
			// nothing to do, constructor only present to avoid synthetic constructor
		}
		
		@Override
		public void keyPressed(final KeyEvent event) {
			clearErrorMessage();
		}
	}
	
	/**
	 * {@link FocusAdapter} for {@code VALIDATE_ON_KEY_STROKE}.
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private final class FocusAdapterValidateOnKeyStroke extends FocusAdapter {
		public FocusAdapterValidateOnKeyStroke() {
			// nothing to do, constructor only present to avoid synthetic constructor
		}
		
		@Override
		public void focusGained(final FocusEvent event) {
			refreshValidState();
		}
		
		@Override
		public void focusLost(final FocusEvent event) {
			clearErrorMessage();
		}
	}
	
	/**
	 * {@link FocusAdapter} for {@code VALIDATE_ON_FOCUS_LOST}.
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private final class FocusAdapterValidateOnFocusLost extends FocusAdapter {
		public FocusAdapterValidateOnFocusLost() {
			// nothing to do, constructor only present to avoid synthetic constructor
		}
		
		@Override
		public void focusGained(final FocusEvent event) {
			refreshValidState();
		}
		
		@Override
		public void focusLost(final FocusEvent event) {
			valueChanged();
			clearErrorMessage();
		}
	}
}
