/*
 * Copyright (C) 2014-2015 Christopher Dillo
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE GUILoggingWindow plug-in.
 * 
 * The ULTIMATE GUILoggingWindow plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE GUILoggingWindow plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE GUILoggingWindow plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE GUILoggingWindow plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE GUILoggingWindow plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.gui.views;

import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.part.*;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.gui.logging.GuiLoggingWindowAppender;

/**
 * simple text showing de.uni_freiburg.informatik.ultimate.gui.logging for the
 * Gui .. so we can see logging messages without an IDE
 * 
 * and for showing other textbased messages.
 * 
 * 
 * @author Christian Ortolf / dietsch
 */
public class LoggingView extends ViewPart {

	/**
	 * the styled text that will contain our logs
	 */
	private StyledText mStyledText;
	private GuiLoggingWindowAppender mAppender;
	private int oldLineCount;

	private Color mColorDebug;
	private Color mColorInfo;
	private Color mColorWarning;
	private Color mColorError;
	private Color mColorFatal;

	public static final String ID = "de.uni_freiburg.informatik.ultimate.gui.views.LoggingView";

	public void createPartControl(Composite parent) {
		oldLineCount = 0;
		parent.setLayout(new GridLayout());
		mStyledText = new StyledText(parent, SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.READ_ONLY | SWT.BORDER);
		mStyledText.setFont(new Font(mStyledText.getFont().getDevice(), "Courier", 10, SWT.NORMAL));
		mStyledText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		mStyledText.addModifyListener(new ModifyListener() {
			public void modifyText(final ModifyEvent e) {
				mStyledText.setSelection(mStyledText.getCharCount());
			}
		});

		UltimatePreferenceStore preferenceStore = new UltimatePreferenceStore(Activator.PLUGIN_ID);

		mAppender = new GuiLoggingWindowAppender();
		mAppender.init();
		mAppender
				.setLayout(new PatternLayout(preferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)));

		// use the root logger to have this appender in all child
		// loggers
		Logger.getRootLogger().addAppender(mAppender);
		Logger.getRootLogger().info("Activated GUI Logging Window for Log4j Subsystem");

		// Listen to preference changes affecting the GUI log output: Pattern
		// and colors
		preferenceStore.addPreferenceChangeListener(new IPreferenceChangeListener() {
			@Override
			public void preferenceChange(PreferenceChangeEvent event) {
				// do things if it concerns the loggers
				String ek = event.getKey();
				if (ek.equals(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)
						|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_DEBUG)
						|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_INFO)
						|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_WARNING)
						|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_ERROR)
						|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_FATAL)) {
					refreshPreferenceProperties();
				}
			}
		});

		refreshPreferenceProperties();
	}

	/**
	 * deletes all text in the textwidget must be called from ui thread
	 * 
	 */
	public void clear() {
		mStyledText.setText("");
		oldLineCount = 0;
	}

	/**
	 * writes a string to the textwidget
	 * 
	 * @param s
	 *            - the string .. callers should prefix with "\n" if they want
	 *            new lines..
	 */
	public void write(String s) {
		mStyledText.append(s);
		for (int i = oldLineCount; i < mStyledText.getLineCount(); ++i) {
			String line = mStyledText.getLine(i);
			String[] splits = line.split(" ");
			if (splits.length < 3) {
				continue;
			}
			String third = splits[2].trim();

			if (third.equals("DEBUG")) {
				mStyledText.setLineBackground(i, 1, mColorDebug);
			} else if (third.equals("INFO")) {
				mStyledText.setLineBackground(i, 1, mColorInfo);
			} else if (third.equals("WARN")) {
				mStyledText.setLineBackground(i, 1, mColorWarning);
			} else if (third.equals("ERROR")) {
				mStyledText.setLineBackground(i, 1, mColorError);
			} else if (third.equals("FATAL")) {
				mStyledText.setLineBackground(i, 1, mColorFatal);
			}
		}
		oldLineCount = mStyledText.getLineCount() - 1;
	}

	@Override
	public void setFocus() {

	}

	@Override
	public void dispose() {
		if (mStyledText != null) {
			mStyledText.dispose();
		}
		super.dispose();
	}

	private void refreshPreferenceProperties() {
		UltimatePreferenceStore preferenceStore = new UltimatePreferenceStore(Activator.PLUGIN_ID);

		mAppender
				.setLayout(new PatternLayout(preferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)));

		mColorDebug = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_DEBUG));
		mColorInfo = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_INFO));
		mColorWarning = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_WARNING));
		mColorError = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_ERROR));
		mColorFatal = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_FATAL));
	}

	/**
	 * Create a Color object with the colour given by a string as in
	 * PreferenceType.Color
	 * 
	 * @param colorString
	 *            Color as "red,green,blue" where 0 <= red, green, blue <= 255
	 * @return a Color object with the given colour
	 */
	private Color colorFromString(String colorString) {
		String[] channels = colorString.split(",");
		if (channels.length >= 3) {
			Color color;
			try {
				color = new Color(Display.getDefault(), Integer.parseInt(channels[0]), Integer.parseInt(channels[1]),
						Integer.parseInt(channels[2]));
			} catch (NumberFormatException e) {
				color = new Color(Display.getDefault(), 255, 255, 255);
			}
			return color;
		}

		// default colour: white
		return new Color(Display.getDefault(), 255, 255, 255);
	}
}
