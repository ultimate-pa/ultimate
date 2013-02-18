package local.stalin.gui.views;


import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.*;

/**
 * simple text showing local.stalin.gui.logging  for the Gui ..
 * so we can see logging messages without an IDE
 * 
 * and for showing other textbased messages.
 * 
 * 
 * @author Christian Ortolf
 */
public class LoggingView extends ViewPart  {

	/**
	 * the styled text that will contain our logs 
	 */
	private StyledText styledText;

	public static final String ID = "local.stalin.gui.views.LoggingView";
	
	/*public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		setSite(site);
		setInput(input);
		setPartName( input.getName());
	}*/

	public void createPartControl(Composite parent) {
		parent.setLayout(new GridLayout());
		styledText = new StyledText(parent,  SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.READ_ONLY | SWT.BORDER);
		styledText.setFont(new Font(styledText.getFont().getDevice(),"Courier", 10, SWT.NORMAL));
		styledText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		styledText.addModifyListener(new ModifyListener() {
			public void modifyText(final ModifyEvent e) {
				styledText.setSelection(styledText.getCharCount());
			}
		});
		
	}

	//@Override
	public void setFocus() {
		//styledText.setFocus();
	}

	/**
	 * deletes all text in the textwidget
	 * must becalled from ui thread
	 *
	 */
	public void clear() {
		styledText.setText("");
	}

	/**
	 * writes a string to the textwidget
	 * @param s - the string .. callers should prefix with "\n" if they want new lines..
	 */
	public void write(String s) {
		styledText.append(s);
	}

	
	
	


}
