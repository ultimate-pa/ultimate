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

import java.io.IOException;
import java.io.Writer;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.part.ViewPart;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.gui.logging.GuiLoggingWindowAppender;

/**
 * simple text showing de.uni_freiburg.informatik.ultimate.gui.logging for the Gui .. so we can see logging messages
 * without an IDE
 *
 * and for showing other textbased messages.
 *
 *
 * @author Christian Ortolf
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class LoggingView extends ViewPart {

	private static final int RGB_LENGTH = 3;
	private static final int RGB_BLUE = 255;
	private static final int RGB_GREEN = 255;
	private static final int RGB_RED = 255;
	private static final int FONT_SIZE = 10;
	public static final String ID = "de.uni_freiburg.informatik.ultimate.gui.views.LoggingView";
	private static final Set<String> RELEVANT_EVENTS = new HashSet<>(Arrays.asList(
			new String[] { CorePreferenceInitializer.LABEL_LOG4J_PATTERN, CorePreferenceInitializer.LABEL_COLOR_DEBUG,
					CorePreferenceInitializer.LABEL_COLOR_INFO, CorePreferenceInitializer.LABEL_COLOR_WARNING,
					CorePreferenceInitializer.LABEL_COLOR_ERROR, CorePreferenceInitializer.LABEL_COLOR_FATAL }));

	private ILoggingService mLoggingService;
	private Writer mLastWriter;

	private StyledText mStyledText;
	private int mOldLineCount;

	private Color mColorDebug;
	private Color mColorInfo;
	private Color mColorWarning;
	private Color mColorError;
	private Color mColorFatal;

	@Override
	public void createPartControl(final Composite parent) {
		mOldLineCount = 0;
		parent.setLayout(new GridLayout());
		mStyledText = new StyledText(parent, SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.READ_ONLY | SWT.BORDER);
		mStyledText.setFont(new Font(mStyledText.getFont().getDevice(), "Courier", FONT_SIZE, SWT.NORMAL));
		mStyledText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		mStyledText.addModifyListener(e -> mStyledText.setSelection(mStyledText.getCharCount()));
	}

	public void initializeLogging(final ILoggingService service) {
		if (service == null) {
			throw new IllegalArgumentException("No service present");
		}
		mLoggingService = service;
		service.getControllerLogger().info("Activated GUI Logging Window for Log4j Subsystem");

		// Listen to preference changes affecting the GUI log output: Pattern
		// and colors
		final RcpPreferenceProvider preferenceStore = new RcpPreferenceProvider(Activator.PLUGIN_ID);
		preferenceStore.addPreferenceChangeListener(this::preferenceChangeListener);
		refreshPreferenceProperties();
	}

	private void preferenceChangeListener(final PreferenceChangeEvent event) {
		// do things if it concerns the loggers
		final String ek = event.getKey();
		if (RELEVANT_EVENTS.contains(ek)) {
			refreshPreferenceProperties();
		}
	}

	/**
	 * deletes all text in the textwidget must be called from ui thread
	 *
	 */
	public void clear() {
		mStyledText.setText("");
		mOldLineCount = 0;
	}

	/**
	 * writes a string to the textwidget
	 *
	 * @param s
	 *            the string that should be written. Callers should add their own linebreaks.
	 */
	public void write(final String s) {
		mStyledText.append(s);
		for (int i = mOldLineCount; i < mStyledText.getLineCount(); ++i) {
			final String line = mStyledText.getLine(i);
			final String[] splits = line.split(" ");
			if (splits.length < 3) {
				continue;
			}
			final String third = splits[2].trim();

			if ("DEBUG".equals(third)) {
				mStyledText.setLineBackground(i, 1, mColorDebug);
			} else if ("INFO".equals(third)) {
				mStyledText.setLineBackground(i, 1, mColorInfo);
			} else if ("WARN".equals(third)) {
				mStyledText.setLineBackground(i, 1, mColorWarning);
			} else if ("ERROR".equals(third)) {
				mStyledText.setLineBackground(i, 1, mColorError);
			} else if ("FATAL".equals(third)) {
				mStyledText.setLineBackground(i, 1, mColorFatal);
			}
		}
		mOldLineCount = mStyledText.getLineCount() - 1;
	}

	@Override
	public void dispose() {
		if (mStyledText != null) {
			mStyledText.dispose();
		}
		if (mLoggingService != null) {
			mLoggingService.removeWriter(mLastWriter);
			mLastWriter = null;
		} else if (mLastWriter != null) {
			try {
				mLastWriter.close();
			} catch (final IOException e) {
				// ignore this IO exception
			}
		}
		final RcpPreferenceProvider preferenceStore = new RcpPreferenceProvider(Activator.PLUGIN_ID);
		preferenceStore.removePreferenceChangeListener(this::preferenceChangeListener);
		super.dispose();
	}

	@Override
	public void setFocus() {
		// not used
	}

	private void renewWriter() {
		if (mLastWriter != null) {
			mLoggingService.removeWriter(mLastWriter);
		}
		mLastWriter = GuiLoggingWindowAppender.createWriter();
		final String layout =
				new RcpPreferenceProvider(Activator.PLUGIN_ID).getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN);
		final ILogger logger = mLoggingService.getControllerLogger();
		mLoggingService.addWriter(mLastWriter, layout);
		logger.debug("Renewed GUI Logging Window");
	}

	private void refreshPreferenceProperties() {
		final RcpPreferenceProvider preferenceStore = new RcpPreferenceProvider(Activator.PLUGIN_ID);
		mColorDebug = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_DEBUG));
		mColorInfo = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_INFO));
		mColorWarning = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_WARNING));
		mColorError = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_ERROR));
		mColorFatal = colorFromString(preferenceStore.getString(CorePreferenceInitializer.LABEL_COLOR_FATAL));
		renewWriter();
	}

	/**
	 * Create a Color object with the colour given by a string as in PreferenceType.Color
	 *
	 * @param colorString
	 *            Color as "red,green,blue" where 0 <= red, green, blue <= 255
	 * @return a Color object with the given colour
	 */
	private static Color colorFromString(final String colorString) {
		final String[] channels = colorString.split(",");
		if (channels.length >= RGB_LENGTH) {
			Color color;
			try {
				color = new Color(Display.getDefault(), Integer.parseInt(channels[0]), Integer.parseInt(channels[1]),
						Integer.parseInt(channels[2]));
			} catch (final NumberFormatException e) {
				color = new Color(Display.getDefault(), RGB_RED, RGB_GREEN, RGB_BLUE);
			}
			return color;
		}

		// default colour: white
		return new Color(Display.getDefault(), RGB_RED, RGB_GREEN, RGB_BLUE);
	}

}
