package de.uni_freiburg.informatik.ultimate.gui.views;

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
	private StyledText styledText;

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
		styledText = new StyledText(parent, SWT.V_SCROLL | SWT.H_SCROLL
				| SWT.MULTI | SWT.READ_ONLY | SWT.BORDER);
		styledText.setFont(new Font(styledText.getFont().getDevice(),
				"Courier", 10, SWT.NORMAL));
		styledText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		styledText.addModifyListener(new ModifyListener() {
			public void modifyText(final ModifyEvent e) {
				styledText.setSelection(styledText.getCharCount());
			}
		});

		mColorDebug = new Color(Display.getDefault(), 223, 223, 223);
		mColorInfo = new Color(Display.getDefault(), 255, 255, 255);
		mColorWarning = new Color(Display.getDefault(), 223, 223, 95);
		mColorError = new Color(Display.getDefault(), 255, 85, 85);
		mColorFatal = new Color(Display.getDefault(), 255, 85, 85);
	}

	/**
	 * deletes all text in the textwidget must be called from ui thread
	 * 
	 */
	public void clear() {
		styledText.setText("");
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
		styledText.append(s);
		for (int i = oldLineCount; i < styledText.getLineCount(); ++i) {
			String line = styledText.getLine(i);
			String[] splits = line.split(" ");
			if (splits.length < 3) {
				continue;
			}
			String third = splits[2].trim();
			
			if (third.equals("DEBUG")) {
				styledText.setLineBackground(i, 1, mColorDebug);
			} else if (third.equals("INFO")) {
				styledText.setLineBackground(i, 1, mColorInfo);
			} else if (third.equals("WARN")) {
				styledText.setLineBackground(i, 1, mColorWarning);
			} else if (third.equals("ERROR")) {
				styledText.setLineBackground(i, 1, mColorError);
			} else if (third.equals("FATAL")) {
				styledText.setLineBackground(i, 1, mColorFatal);
			}
		}
		oldLineCount = styledText.getLineCount() - 1;
	}

	@Override
	public void setFocus() {
		
	}

}
